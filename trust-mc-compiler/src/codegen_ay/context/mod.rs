// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! AY Codegen Context.

mod artifact;
mod config;
mod heap;
mod memory;
mod playback;
mod properties;
mod shadow_mem_ctx;
#[cfg(test)]
mod testing;

use crate::callee_body::CalleeBody;
use crate::kani_middle::std_abstraction::StdAbstraction;
use crate::kani_middle::transform::BodyTransformation;
use crate::kani_queries::QueryDb;
use ay_bindings::{AYProgram, Expr, Sort, SortInner};
use rustc_data_structures::fx::{FxHashMap, FxIndexMap};
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::mono::Instance;
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::sync::Arc;
use trust_mc_core::artifact::PropertyMetadata;
use trust_mc_core::bmc::BmcVc;
use trust_mc_core::chc::ChcVc;
use trust_mc_core::decl::Decl;

pub(in crate::codegen_ay) use config::AYConfig;
pub(in crate::codegen_ay) use heap::{BoxPointerOrigin, HeapState};
pub(in crate::codegen_ay) use properties::CheckGate;
pub(in crate::codegen_ay) use properties::get_unconstrained_assignment_count;
pub(in crate::codegen_ay) use properties::get_unsupported_construct_fallback_count;
#[cfg(test)]
#[allow(unused_imports)]
pub(in crate::codegen_ay) use properties::set_unconstrained_assignment_count_for_test;
#[cfg(test)]
#[allow(unused_imports)]
pub(in crate::codegen_ay) use properties::set_unsupported_construct_fallback_count_for_test;
pub(in crate::codegen_ay) use properties::take_unconstrained_assignment_count;
pub(in crate::codegen_ay) use properties::take_unsupported_construct_fallback_count;

/// Minimal context for tracking codegen results after splitting from main context.
///
/// Used to return diagnostics without retaining the full codegen state.
#[derive(Debug, Default)]
pub(in crate::codegen_ay) struct MinimalAYCtx {
    /// Map of unsupported construct names to locations where they occurred.
    /// Keys are `&'static str` because all construct names are string literals,
    /// avoiding a `.to_owned()` allocation per `unsupported()` call. Part of #2267.
    pub(in crate::codegen_ay) unsupported_constructs: FxHashMap<&'static str, Vec<String>>,
}

/// Main context for AY code generation.
///
/// Holds all state needed to translate MIR into SMT-LIB2 constraints.
/// Manages the AY program being built, variable declarations, memory model,
/// and tracks any unsupported constructs encountered during codegen.
///
/// # Lifetime Parameters
/// - `'tcx`: Rust type context lifetime (from TyCtxt)
/// - `'t`: Transformer lifetime - AYCtx cannot outlive the BodyTransformation
///
/// The `'t` lifetime provides compiler-enforced safety: AYCtx cannot outlive
/// the transformer reference, preventing use-after-free (#564).
pub(in crate::codegen_ay) struct AYCtx<'tcx, 't> {
    /// Rust type context for querying type information.
    pub(in crate::codegen_ay) tcx: TyCtxt<'tcx>,
    /// Kani query database for configuration and attributes.
    pub(in crate::codegen_ay) queries: QueryDb,
    /// Backend configuration (unwind depth, CHC mode, logic).
    pub(in crate::codegen_ay) config: AYConfig,
    /// The harness body has no obligation SITE at all — no `Call`, no `Assert`
    /// terminator. Recorded during codegen (the artifact builder has no
    /// `Instance` to fetch a body with) and surfaced to the driver so its
    /// vacuity refusal can tell "nothing to prove" from "we dropped it".
    /// Per-HARNESS obligation-free certificates, keyed by the name
    /// `build_artifact` is called with.
    ///
    /// This was a single `bool`, which one `AYCtx` serving several harnesses in
    /// one file made meaningless: `codegen_function_with_body` runs per
    /// function, so whichever ran LAST decided the answer for every artifact.
    /// A file whose second harness has no obligation could hand its
    /// certificate to a first harness that does — a false-Safe channel — and
    /// the reverse cost parity. Measured on `obligation_free_walk_dual_safe.rs`,
    /// where both safe twins went VACUOUS.
    pub(in crate::codegen_ay) obligation_free_body_by_fn: std::collections::HashMap<String, bool>,
    /// The standard-library code the inline gate keeps as calls, resolved
    /// once for the unit (`kani_middle::std_abstraction`).
    pub(in crate::codegen_ay) std_abstraction: StdAbstraction,
    /// The AY program being constructed (holds SMT commands).
    pub(in crate::codegen_ay) program: AYProgram,
    /// Abstract BMC verification condition (dual-write for migration).
    ///
    /// During migration from direct AYProgram construction to trust_mc_core IR,
    /// we populate both `program` and `bmc_vc`. Once migration is complete,
    /// `program` will be replaced by `emit_bmc(bmc_vc)` at finalization.
    pub(in crate::codegen_ay) bmc_vc: BmcVc,
    /// CHC verification condition for Horn clause mode.
    ///
    /// Populated by `mir_to_chc` when `config.use_chc` is true.
    /// Used by `split_emit_chc` at finalization to generate the Horn clause program.
    pub(in crate::codegen_ay) chc_vc: Option<ChcVc>,
    /// Map of variable names to their AY expressions.
    var_map: HashMap<Arc<str>, Expr>,
    /// Array-based memory model expression.
    memory: Option<Expr>,
    /// Addresses that received non-bitvec symbolic stores (Int, Array, Datatype).
    ///
    /// Maps coerced address → symbolic value expression for recovery on matching
    /// non-bitvec raw-pointer loads and for fail-closed byte-load guards.
    /// Part of #2599.
    symbolic_memory_stores: HashMap<Expr, Expr>,
    /// Counter for generating unique names.
    name_counter: u64,
    /// Counter for generating unique assertion labels.
    label_counter: u64,
    /// Counter for generating unique property IDs (for trust_mc_core Violation).
    property_counter: u32,
    /// Context for the function currently being codegen'd.
    current_fn: Option<CurrentFnCtx>,
    /// Sticky per-inline-call SSA-namespace salt. When `Some(n)`, every
    /// `set_current_fn` appends `#f{n}` to the frame name, so ALL callee-frame
    /// SSA variables produced during that inline (top-level AND nested) land in a
    /// disjoint namespace. Set once per bounded-unroll iteration
    /// (`codegen_iter_all_any`) so repeated inlinings of the SAME predicate
    /// closure over distinct elements do NOT share a frame — sharing would force
    /// the two elements' reference evaluations equal (a vacuous verify). `None`
    /// (the default) leaves frame names untouched, so all non-unroll paths are
    /// unaffected.
    inline_frame_salt: Option<u64>,
    /// Monotonic source of fresh `inline_frame_salt` values, so nested unrolls
    /// never collide on a reused loop index.
    inline_frame_salt_counter: u64,
    /// Unsupported MIR constructs encountered (for diagnostics).
    /// Keys are `&'static str` — all construct names are string literals. Part of #2267.
    pub(in crate::codegen_ay) unsupported_constructs: FxHashMap<&'static str, Vec<String>>,
    /// Reference to body transformer for accessing transformed MIR bodies.
    ///
    /// The lifetime `'t` ensures compiler-enforced safety: AYCtx cannot outlive
    /// the transformer reference. This replaces the previous raw pointer pattern
    /// that relied on documented invariants rather than compiler enforcement (#564).
    ///
    /// `None` is allowed for testing contexts that don't need `body()` access.
    transformer: Option<&'t mut BodyTransformation>,
    /// Boolean predicates for property violations in the current harness.
    ///
    /// We build a single counterexample query of the form:
    /// `constraints ∧ (or violations...)`
    property_violations: Vec<Expr>,
    /// Ordered assumption context for Kani assert-assume semantics.
    ///
    /// CBMC/Kani `assume` (including the assume half of assert-assume)
    /// constrains only the program suffix: checks recorded after it. A global
    /// `(assert ...)` would retroactively mask earlier failures, so suffix
    /// assumptions are folded into this chained Bool predicate, which
    /// subsequent violation/cover/reach flags conjoin. `None` = no suffix
    /// assumptions recorded yet (context is trivially `true`).
    assumption_context: Option<Expr>,
    /// Guard, value and replayability queries for each playback input, in creation order.
    any_vars: Vec<Expr>,
    /// Cover property predicates for reachability checks (kani::cover).
    ///
    /// Unlike violations (which are OR'd for counterexample search), cover properties
    /// are checked separately for satisfiability. Each cover property represents a
    /// reachability condition that the verifier reports as SATISFIED/UNSATISFIED.
    ///
    /// Only predicate expressions are needed at query time; source/name metadata
    /// is tracked separately in `cover_metadata` for artifact emission.
    cover_properties: Vec<Expr>,
    /// Cover property metadata for VC artifact emission (#1164).
    ///
    /// Stores source location and other metadata for cover properties,
    /// separate from the expressions in `cover_properties` to support
    /// artifact serialization without exposing ay_bindings::Expr.
    cover_metadata: Vec<PropertyMetadata>,
    /// Source coverage predicates for `StatementKind::Coverage`.
    ///
    /// These are queried separately from verification assertions so coverage
    /// reporting cannot change proof success or failure.
    coverage_properties: Vec<Expr>,
    /// Source coverage metadata for VC artifact emission.
    coverage_metadata: Vec<PropertyMetadata>,
    /// Heap allocation model state for AY backend (#1100).
    ///
    /// Tracks allocation metadata:
    /// - Object validity (which allocations are alive)
    /// - Object sizes (for deallocation size checking)
    /// - Fresh allocation ID generator
    heap_state: HeapState,
    /// Scalar shadow-memory init-tracking state (MEMUB-24/25/27).
    ///
    /// Lives on the ctx (not the per-frame `StatementCodegen`) so it threads
    /// through mini-inlined callee bodies, like the heap model.
    shadow_mem: shadow_mem_ctx::BmcShadowMemState,
    /// Mapping from MIR local indices to CHC state argument indices, keyed by function name.
    ///
    /// Populated in CHC mode to canonicalize loop invariant hints.
    chc_local_to_state_idx: HashMap<Arc<str>, HashMap<usize, usize>>,
    /// BMC mini-inline call stack of currently-inlining instance names.
    ///
    /// The BMC statement-dispatch path (`try_inline_small_instance_call`)
    /// recursively descends into callee bodies during translation. Without a
    /// guard, a self-recursive Rust function (e.g. `fn f(n: u32) -> u32 { ...
    /// f(n - 1) }`) drives the dispatcher into unbounded host-stack recursion,
    /// crashing rustc with a stack overflow. The CHC inliner already tracks
    /// `inline_depth` via `MAX_INLINE_DEPTH`; this stack is the BMC analogue.
    ///
    /// Push the callee key on entry, pop on exit. If the key is already on the
    /// stack (recursive cycle) or the depth exceeds the cap, the dispatcher
    /// declines to inline and the caller falls through to a non-inlining path.
    /// Part of #recursive-sum-stack-overflow.
    pub(in crate::codegen_ay) bmc_mini_inline_stack: Vec<String>,
    /// Name of the ROOT function of the BMC codegen unit — the body
    /// `codegen_function` entered — recorded by `set_current_fn` only while no
    /// inline frame is active (no frame salt, empty `bmc_mini_inline_stack`).
    /// Per-harness unsoundness records made inside an inlined callee are
    /// charged to this name rather than to the callee's salted frame name, so
    /// the driver attributes the taint to the harness that executes it.
    pub(in crate::codegen_ay) bmc_root_fn_name: Option<String>,
    /// BMC lane: the `memory` array as first declared for this harness, before
    /// any store. Global allocations (statics, constant memory) constrain their
    /// initializer bytes on it, not on the current store chain.
    pub(in crate::codegen_ay) initial_memory: Option<Expr>,
    /// BMC lane: THE address symbol of each global allocation (a static or
    /// constant memory) this harness names, keyed by
    /// `shared::const_pointer::TargetKey` (`statement::global_alloc`). Shared by the raw-pointer
    /// lane and the constant-reference lane, so one static never gets two
    /// unrelated addresses. It lives exactly as long as `alloc_roots` and the
    /// heap's registered stack objects, which hold the same symbols: clearing
    /// it alone would re-register a symbol and make its disjointness
    /// constraint contradict itself.
    pub(in crate::codegen_ay) global_alloc_addrs:
        HashMap<crate::codegen_ay::shared::const_pointer::TargetKey, Expr>,
    /// BMC lane: the keys of `global_alloc_addrs` whose initializer bytes are
    /// constrained on `initial_memory`.
    pub(in crate::codegen_ay) global_alloc_bytes:
        HashSet<crate::codegen_ay::shared::const_pointer::TargetKey>,
    /// Byte extent of every allocation the BMC lane can NAME, keyed by the
    /// SMT variable that is its base: the stable address symbol minted for an
    /// address-taken local (`rvalue_address_of`), registered from the local's
    /// sized layout. The pointer-offset obligations (`ptr::offset` /
    /// `add` / `sub` / `offset_from`) read it to decide Kani's same-allocation
    /// check structurally; a base that is not here is an allocation the encoder
    /// cannot name, and those sites fail closed (`bmc_offset_provenance_unresolved`).
    pub(in crate::codegen_ay) alloc_views: HashMap<String, AllocView>,
    /// Root local -> (allocation base term, extent) of the first registered
    /// view, so a second view of the same local is tied to the same base.
    /// Insertion-ordered: each new root is asserted apart from the roots
    /// registered before it in this order, so the SMT text is the same on every
    /// run. A std `HashMap` here emitted those assertions in a per-process
    /// random order, and BMC verdicts that are sensitive to assertion order
    /// flipped from run to run on one bundle (measured 2026-10-01 on
    /// `loop_contract_register_walk_dual.rs::inv_oob_bug`: two runs of main's
    /// bundle handed `ay` the same assertions in two orders, FAILED once and
    /// INCONCLUSIVE once).
    ///
    /// Any fixed order is a choice, because `ay` is not order-blind
    /// (`docs/ay-asks/2026-10-01-bmc-assertion-order-sensitivity-48c98a43d/`).
    /// At `ay` 48c98a43d this order left
    /// `dual_p3_splice_stale_cex.rs::splice_stale_cex` undecided and the earlier
    /// roots sorted by printed base term decided it, so `88cac3af1` used that
    /// order. Re-measured at `ay` d80d17a90 (2026-10-14) on the 146 dual
    /// harnesses whose texts the two orders change, it no longer pays: one CLI
    /// round gave every one the same answer in both orders, four rounds of the
    /// 28 slowest moved only two budget-edge rows, and those trade:
    /// `splice_stale_cex` [bmc] was decided in 17 of 17 driver runs in this
    /// order and 9 of 17 sorted, `safe_clamp_through_generic` [bmc] in 4 of 6
    /// here and 6 of 6 sorted. Registration order is main's and is kept.
    pub(in crate::codegen_ay) alloc_roots: FxIndexMap<Arc<str>, (Expr, u128)>,
    /// Address symbols whose view changed on reuse: never a named allocation.
    pub(in crate::codegen_ay) alloc_views_poisoned: HashSet<String>,
    /// Merge (phi) definitions `phi_var = ite(pred, v1, ite(..))`, keyed by the
    /// phi variable. Read ONLY by the allocation resolver (alloc_view.rs): the
    /// phi RHS is not cached in `ssa_concrete_values`, whose other readers
    /// would change meaning on an `ite` root.
    pub(in crate::codegen_ay) alloc_phi_defs: HashMap<String, Expr>,
}

/// Where an address symbol sits inside the allocation it points into
/// (BMC lane, `statement/alloc_view.rs`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay) struct AllocView {
    /// SSA base name of the root local: equal roots are one allocation.
    pub(in crate::codegen_ay) root: Arc<str>,
    /// Byte offset of the symbol's place from the start of the root local.
    pub(in crate::codegen_ay) offset: u128,
    /// Size of the root local in bytes.
    pub(in crate::codegen_ay) extent: u128,
}

/// Context for the function currently being code-generated.
#[derive(Debug, Clone)]
pub(in crate::codegen_ay) struct CurrentFnCtx {
    /// Monomorphized function instance currently being encoded.
    pub(in crate::codegen_ay) instance: Instance,
    /// Function name for naming conventions.
    pub(in crate::codegen_ay) name: String,
}

impl<'tcx, 't> AYCtx<'tcx, 't> {
    /// The names of the property-violation predicates recorded so far
    /// (`ay_violation_<label>_<n>`), for tests.
    #[cfg(test)]
    pub(in crate::codegen_ay) fn property_violation_names(&self) -> Vec<String> {
        self.property_violations
            .iter()
            .filter_map(|pred| match pred.value() {
                ay_bindings::ExprValue::Var { name } => Some(name.clone()),
                _ => None,
            })
            .collect()
    }

    /// Create a new AY codegen context.
    ///
    /// Initializes the AYProgram with the appropriate mode (BMC or CHC)
    /// based on the provided configuration.
    pub(in crate::codegen_ay) fn new(
        tcx: TyCtxt<'tcx>,
        queries: QueryDb,
        config: AYConfig,
        transformer: &'t mut BodyTransformation,
    ) -> Self {
        let mut program = if config.use_chc {
            AYProgram::horn()
        } else {
            // Use the configured logic, defaulting to QF_AUFBV for BMC
            let mut prog = AYProgram::new();
            prog.set_logic(&config.logic);
            prog
        };

        if config.produce_models {
            program.produce_models();
        }

        // Initialize BmcVc with query configuration (dual-write for migration)
        // Note: Logic selection happens here with has_datatypes=false as placeholder;
        // actual datatype presence is handled by upgrade_logic_for_datatypes later.
        let mut bmc_vc = BmcVc::new();
        bmc_vc.query.produce_model = config.produce_models;
        bmc_vc.query.logic = Some(config.select_logic(false).to_owned());

        Self {
            tcx,
            queries,
            config,
            obligation_free_body_by_fn: std::collections::HashMap::new(),
            std_abstraction: StdAbstraction::resolve(tcx),
            program,
            bmc_vc,
            chc_vc: None,
            var_map: HashMap::new(),
            memory: None,
            symbolic_memory_stores: HashMap::new(),
            name_counter: 0,
            label_counter: 0,
            property_counter: 0,
            current_fn: None,
            inline_frame_salt: None,
            inline_frame_salt_counter: 0,
            unsupported_constructs: FxHashMap::default(),

            transformer: Some(transformer),
            property_violations: Vec::new(),
            assumption_context: None,
            any_vars: Vec::new(),
            cover_properties: Vec::new(),
            cover_metadata: Vec::new(),
            coverage_properties: Vec::new(),
            coverage_metadata: Vec::new(),
            heap_state: HeapState::new(),
            shadow_mem: shadow_mem_ctx::BmcShadowMemState::default(),
            chc_local_to_state_idx: HashMap::new(),
            bmc_mini_inline_stack: Vec::new(),
            bmc_root_fn_name: None,
            initial_memory: None,
            global_alloc_addrs: HashMap::new(),
            global_alloc_bytes: HashSet::new(),
            alloc_views: HashMap::new(),
            alloc_roots: FxIndexMap::default(),
            alloc_views_poisoned: HashSet::new(),
            alloc_phi_defs: HashMap::new(),
        }
    }

    /// This codegen unit's stub map, empty when there is no transformer.
    pub(in crate::codegen_ay) fn transformer_stub_map(
        &self,
    ) -> crate::codegen_ay::obligation_free_walk::StubMap {
        self.transformer.as_ref().map(|t| t.stub_map_for_walk()).unwrap_or_default()
    }

    /// Get the MIR body for an instance.
    ///
    /// # Panics
    /// Panics if AYCtx was created without a transformer (testing context).
    pub(in crate::codegen_ay) fn body(&mut self, instance: Instance) -> rustc_public::mir::Body {
        self.transformer
            .as_mut()
            .expect("body() called on AYCtx without transformer")
            .body(self.tcx, instance)
    }

    /// Get the MIR body for an instance, falling back to rustc MIR when the
    /// lightweight test context was created without a transformer.
    pub(in crate::codegen_ay) fn body_or_instance_body(
        &mut self,
        instance: Instance,
    ) -> Option<rustc_public::mir::Body> {
        // A float intrinsic Trust core renamed reaches trust-mc's model or fails closed; it
        // never runs Trust's fallback body. On the frozen nightly the call has no body at all,
        // and on Trust `minimum_number_nsz_*` / `maximum_number_nsz_*` carry one that returns
        // a single one of the results the intrinsic may produce (`y` whenever the arguments
        // compare equal), so executing it proved `(-0.0f16).min(0.0).is_sign_positive()`,
        // which fails when the program runs. Every codegen consumer of callee bodies (the BMC
        // mini-inliner and its closure, fn-pointer and iterator-adapter callers) comes through
        // here, so none of them can reach that body. See
        // `intrinsics::is_modelled_renamed_intrinsic`; always false on the nightly.
        if crate::intrinsics::is_modelled_renamed_intrinsic(&instance) {
            return None;
        }
        if let Some(transformer) = self.transformer.as_mut() {
            // `try_body`, not `body`: the latter panics on an instance with no
            // MIR, which made this function's `Option` a promise it could not
            // keep on the transformer path. Callers already handle `None`.
            return transformer.try_body(self.tcx, instance);
        }
        instance.callee_body()
    }

    /// Install a thread-local snapshot of the body transformer for the CHC
    /// inline walker (see `kani_middle::transform::walker_transformed_body`).
    ///
    /// Returns a scope guard that uninstalls the snapshot on drop; `None` when
    /// this context was built without a transformer (lightweight tests).
    pub(in crate::codegen_ay) fn install_walker_transformer(
        &self,
    ) -> Option<crate::kani_middle::transform::WalkerTransformerScope> {
        self.transformer
            .as_deref()
            .map(crate::kani_middle::transform::WalkerTransformerScope::install)
    }

    /// The unit's stub map (`#[kani::stub]`), for scans that must inspect the
    /// body the unit runs; empty without a transformer (lightweight tests).
    pub(in crate::codegen_ay) fn unit_stub_map(&self) -> crate::kani_middle::codegen_units::Stubs {
        self.transformer.as_deref().map(|t| t.stub_map_for_walk()).unwrap_or_default()
    }

    pub(in crate::codegen_ay) fn record_chc_local_to_state_idx(
        &mut self,
        fn_name: impl Into<Arc<str>>,
        mapping: HashMap<usize, usize>,
    ) {
        self.chc_local_to_state_idx.insert(fn_name.into(), mapping);
    }

    /// Generate a fresh unique name with the given prefix.
    pub(in crate::codegen_ay) fn fresh_name(&mut self, prefix: &str) -> String {
        let n = self.name_counter;
        self.name_counter += 1;
        let mut name = String::with_capacity(prefix.len() + 1 + 20);
        name.push_str(prefix);
        name.push('_');
        let _ = write!(&mut name, "{n}");
        name
    }

    /// Generate a fresh unique name from `{prefix}_{suffix}`.
    ///
    /// Avoids the intermediate `format!("{prefix}_{suffix}")` allocation
    /// that callers would need when using `fresh_name`. Part of #2267.
    pub(in crate::codegen_ay) fn fresh_name_with_suffix(
        &mut self,
        prefix: &str,
        suffix: &str,
    ) -> String {
        let n = self.name_counter;
        self.name_counter += 1;
        let mut name = String::with_capacity(prefix.len() + 1 + suffix.len() + 1 + 20);
        name.push_str(prefix);
        name.push('_');
        name.push_str(suffix);
        name.push('_');
        let _ = write!(&mut name, "{n}");
        name
    }

    #[must_use]
    fn cache_var_expr(&mut self, name: Arc<str>, expr: Expr) -> Expr {
        self.var_map.insert(name, expr.clone());
        expr
    }

    /// Declare a symbolic variable with the given name and sort.
    ///
    /// Returns the existing variable if one with that name was already declared.
    ///
    /// # Panics
    /// Panics if the name was already declared with a different sort.
    ///
    /// If the sort is a Datatype, this also emits a `(declare-datatype ...)` command
    /// before the variable declaration (if not already declared).
    #[must_use]
    pub(in crate::codegen_ay) fn declare_var(&mut self, name: &str, sort: Sort) -> Expr {
        if let Some(existing) = self.var_map.get(name) {
            return existing.clone();
        }

        // Avoid emitting duplicate `(declare-const ...)` commands, which many SMT solvers reject.
        if let Some(existing_sort) = self.program.get_sort(name) {
            assert_eq!(
                existing_sort, &sort,
                "Attempted to redeclare `{name}` with mismatched sort {sort:?} (existing {existing_sort:?})"
            );
            // Expr::var accepts impl Into<String>, so pass &str directly
            // (one allocation inside Expr::var). Arc<str> for cache key.
            let expr = Expr::var(name, sort);
            return self.cache_var_expr(Arc::from(name), expr);
        }

        // Ensure datatype sorts are declared before use.
        self.ensure_datatype_declared(&sort);

        // Dual-write: add to both program and bmc_vc
        let expr = self.program.declare_const(name, sort.clone());
        self.bmc_vc.add_decl(Decl::constant(name, sort));
        self.cache_var_expr(Arc::from(name), expr)
    }

    /// Ensure that if the sort is a datatype, it is declared in the program.
    ///
    /// SMT-LIB2 requires datatypes to be declared before use. This method
    /// recursively declares any datatype sorts, including those nested in
    /// array element types or datatype fields.
    ///
    /// Dual-writes to both `program` and `bmc_vc` to support both legacy
    /// and emit_bmc paths (#893 Phase 4 fix).
    pub(in crate::codegen_ay) fn ensure_datatype_declared(&mut self, sort: &Sort) {
        let mut visited = HashSet::new();
        self.ensure_datatype_declared_inner(sort, &mut visited);
    }

    /// Inner recursive helper with cycle detection via `visited` set.
    /// Prevents stack overflow on self-referential datatypes (e.g., `List<Box<List>>`).
    /// Part of #2372.
    fn ensure_datatype_declared_inner(&mut self, sort: &Sort, visited: &mut HashSet<String>) {
        match sort.inner() {
            SortInner::Datatype(dt) => {
                // Cycle detection: skip if we've already started processing this type
                if !visited.insert(dt.name.clone()) {
                    return;
                }
                // Recursively ensure field datatypes are declared first
                for cons in &dt.constructors {
                    for field in &cons.fields {
                        self.ensure_datatype_declared_inner(&field.sort, visited);
                    }
                }
                // Declare this datatype if not already declared
                // Dual-write: add to both program and bmc_vc
                // Arc-wrap once, share between both consumers
                if !self.program.is_datatype_declared(&dt.name) {
                    let arc_dt = std::sync::Arc::new(dt.clone());
                    self.program.declare_datatype(ay_bindings::DatatypeSort::clone(&arc_dt));
                    self.bmc_vc.add_decl(Decl::datatype_arc(arc_dt));
                }
            }
            SortInner::Array(arr) => {
                // Check both index and element sorts for nested datatypes
                self.ensure_datatype_declared_inner(&arr.index_sort, visited);
                self.ensure_datatype_declared_inner(&arr.element_sort, visited);
            }
            // Primitive and theory sorts don't need declaration
            SortInner::Bool
            | SortInner::BitVec(_)
            | SortInner::Int
            | SortInner::Real
            | SortInner::String
            | SortInner::FloatingPoint(_, _)
            | SortInner::Uninterpreted(_)
            | SortInner::RegLan => {}
            _ => {}
        }
    }

    /// Look up a declared variable by name.
    pub(in crate::codegen_ay) fn lookup_var(&self, name: &str) -> Option<&Expr> {
        self.var_map.get(name)
    }

    /// Set the current function being code-generated.
    ///
    /// When an `inline_frame_salt` is active, the frame name is suffixed with
    /// `#f{salt}` so that repeated inlinings of the same instance (e.g. one
    /// predicate closure applied to each element of a bounded `.all()`/`.any()`
    /// unroll) land in disjoint SSA namespaces. The salt is sticky across nested
    /// `set_current_fn` calls, so the WHOLE call subtree of one unroll iteration
    /// is namespaced consistently.
    pub(in crate::codegen_ay) fn set_current_fn(&mut self, instance: Instance) {
        let mut name = instance.name();
        if let Some(salt) = self.inline_frame_salt {
            use std::fmt::Write;
            let _ = write!(name, "#f{salt}");
        }
        if self.inline_frame_salt.is_none() && self.bmc_mini_inline_stack.is_empty() {
            self.bmc_root_fn_name = Some(name.clone());
        }
        self.current_fn = Some(CurrentFnCtx { instance, name });
    }

    /// Restore a previously-captured `CurrentFnCtx` verbatim (name included),
    /// without re-deriving the name through the active `inline_frame_salt`. Used
    /// to pop an inline frame back to its parent so the parent keeps the exact
    /// namespace it had on entry.
    pub(in crate::codegen_ay) fn restore_current_fn(&mut self, ctx: Option<CurrentFnCtx>) {
        self.current_fn = ctx;
    }

    /// Set (or clear) the sticky inline-frame salt, returning the previous value
    /// so the caller can restore it (supports nested unrolls).
    pub(in crate::codegen_ay) fn set_inline_frame_salt(
        &mut self,
        salt: Option<u64>,
    ) -> Option<u64> {
        std::mem::replace(&mut self.inline_frame_salt, salt)
    }

    /// Allocate a fresh, globally-unique inline-frame salt value.
    pub(in crate::codegen_ay) fn next_inline_frame_salt(&mut self) -> u64 {
        let v = self.inline_frame_salt_counter;
        self.inline_frame_salt_counter += 1;
        v
    }

    /// Clear the current function context and per-function caches.
    ///
    /// `var_map` is a cache that grows across functions since `program` retains
    /// all declarations. Clearing it avoids unbounded memory growth in
    /// multi-harness verification. Part of #2372.
    pub(in crate::codegen_ay) fn reset_current_fn(&mut self) {
        self.current_fn = None;
        self.bmc_root_fn_name = None;
        self.var_map.clear();
        self.symbolic_memory_stores.clear();
        self.memory = None;
        self.initial_memory = None;
    }

    /// Get the current function context, if any.
    pub(in crate::codegen_ay) fn current_fn(&self) -> Option<&CurrentFnCtx> {
        self.current_fn.as_ref()
    }

    /// Get the current function name, or "unknown" if no function is active.
    ///
    /// Avoids the repeated `.map(|f| f.name.clone()).unwrap_or_else(|| "unknown".to_owned())`
    /// pattern that allocates a new String on every call.
    pub(in crate::codegen_ay) fn current_fn_name(&self) -> &str {
        self.current_fn.as_ref().map_or("unknown", |f| f.name.as_str())
    }

    /// Attribution key for a per-harness unsoundness record made from BMC
    /// statement codegen: the root function of the unit when known, else the
    /// current frame name. A key that names no proof harness is still counted
    /// by the driver against EVERY harness of the crate
    /// (`demotion::attributable_to_harness`, fail-closed), so a wrong key costs
    /// precision, never soundness.
    pub(in crate::codegen_ay) fn bmc_attribution_fn_name(&self) -> &str {
        self.bmc_root_fn_name.as_deref().unwrap_or_else(|| self.current_fn_name())
    }

    /// Finalize using the abstract IR path (emit_bmc).
    ///
    /// This uses `emit_bmc(bmc_vc)` to generate the AY program from the abstract
    /// BMC verification condition, rather than the legacy direct-construction path.
    ///
    /// This is the target architecture for #206: MIR → trust_mc_core IR → emit_bmc → AYProgram.
    ///
    /// Populates model queries with any_raw variables for concrete playback.
    /// Note: emit_bmc automatically adds violation predicates to get-value.
    pub(in crate::codegen_ay) fn finalize_emit_bmc(&mut self) {
        // The vacuity probe needs the whole-trace assumption conjunction
        // (dual-written, so the emit_bmc lane carries it too).
        self.emit_assume_final_flag();
        // Populate model queries for concrete playback.
        // emit_bmc automatically handles violation predicates (ay_viol_*),
        // so we only need to add the kani::any_raw symbolic variables here.
        let queries = self.playback_model_queries();
        self.bmc_vc.model_queries.extend(queries);
    }

    /// Split the context into diagnostics and the generated program.
    ///
    /// Consumes self and returns the minimal diagnostic context plus the AY program.
    ///
    /// Uses the legacy direct-construction path (self.program).
    /// See `split_emit_bmc` for the abstract IR path.
    pub(in crate::codegen_ay) fn split(self) -> (MinimalAYCtx, AYProgram) {
        (MinimalAYCtx { unsupported_constructs: self.unsupported_constructs }, self.program)
    }

    /// Split the context using the abstract IR path (emit_bmc).
    ///
    /// Similar to `split`, but generates the AY program from `bmc_vc` using
    /// `emit_bmc` instead of using the directly-constructed `self.program`.
    ///
    /// Call `finalize_emit_bmc()` before this to populate model queries.
    pub(in crate::codegen_ay) fn split_emit_bmc(self) -> (MinimalAYCtx, AYProgram) {
        // emit_bmc takes BmcVc by value — move self.bmc_vc (no clone)
        let program =
            super::emitter::emit_bmc_with_logic_override(self.bmc_vc, self.config.logic_override);
        (MinimalAYCtx { unsupported_constructs: self.unsupported_constructs }, program)
    }

    /// Split the context using the CHC path (emit_chc).
    ///
    /// Generates the AY program from `chc_vc` using `emit_chc`.
    /// Used when `config.use_chc` is true for unbounded verification via PDR.
    ///
    /// If `chc_vc` is None (CHC codegen was not performed), logs a warning
    /// and returns an empty HORN program as a graceful fallback.
    pub(in crate::codegen_ay) fn split_emit_chc(self) -> (MinimalAYCtx, AYProgram) {
        use super::emit_chc;

        // Move chc_vc by value into emit_chc (no clone)
        let program = if let Some(mut chc_vc) = self.chc_vc {
            // Part of #112: Strip dead relation arguments before emitting.
            // MIR-level encoding creates state variables for all local types
            // and metadata arrays, many of which are never read. Removing them
            // reduces predicate arity, helping PDR converge on loop invariants.
            //
            // Part of #3148: DISABLED — strip_dead_args over-strips variables
            // in harnesses with complex heap patterns (e.g. box_alloc
            // test_box_independence). Cross-relation liveness propagation
            // (#3151) fixed ay_watched (8/8) and ay_literal (5/5), but
            // store/select patterns in multi-allocation harnesses remain
            // theory-unaware. AY upstream DPE (ay#5826) handles this
            // correctly; this pass is superseded once AY DPE is active.
            // Re-enable with TRUST_MC_STRIP_DEAD_ARGS=1 for debugging/benchmarking.
            let strip_enabled =
                std::env::var("TRUST_MC_STRIP_DEAD_ARGS").map(|v| v == "1").unwrap_or(false);
            if strip_enabled {
                let stripped = chc_vc.strip_dead_args();
                if stripped > 0 {
                    tracing::debug!(stripped, "CHC: stripped dead relation arguments (#112)");
                }
            }

            // Part of #3371: Propagate constants through identity chains.
            // When a relation parameter is always the same constant literal
            // across all rules, remove it and add explicit equality constraints.
            // Reduces relation arity, helping PDR converge on invariants.
            let const_prop_disabled_by_env =
                std::env::var("TRUST_MC_NO_CONST_PROP").map(|v| v == "1").unwrap_or(false);
            // SOUNDNESS: the const-prop / orphan-prune / dead-scalar / scalarize
            // sequence can reduce certain VCs into a form whose genuinely-reachable
            // error edge is then dropped or mis-evaluated by the downstream
            // straight-line discharge (which unsoundly proves the reduced VC safe)
            // or by ay's PDR (which false-proves the reduced symbolic form). Leave
            // these VCs unreduced so the un-weakened error obligation survives to
            // the solver. Covers:
            //   - ay#9227 realloc stale-pointer (scalarized `obj_valid_at_*`);
            //   - constant-address heap OOB, e.g. realloc/shrink (scalarized heap
            //     memory cells whose `obj_size` bound const-prop otherwise drops);
            //   - pointer byte-offset overflow (a `bvsdiv`/`sign_extend` overflow
            //     error edge the reduced form mis-folds as satisfied).
            // An *acyclic* contract harness gains nothing from const-prop's
            // arity reduction (no loop invariant for PDR), but const-prop can
            // weaken a violated postcondition edge into a form the discharge/PDR
            // false-proves. Skip it there; cyclic contract harnesses keep it.
            let const_prop_disabled_for_heap_liveness =
                chc_requires_unreduced_obligations(&chc_vc, self.config.is_contract_proof);
            if const_prop_disabled_for_heap_liveness && !const_prop_disabled_by_env {
                tracing::debug!(
                    "CHC: skipped constant propagation to preserve a reachable safety obligation"
                );
            }
            let const_prop_disabled =
                const_prop_disabled_by_env || const_prop_disabled_for_heap_liveness;
            // Part of #argorder: snapshot the well-formed VC before the
            // optimization passes below. Constant propagation / scalarization /
            // dead-arg pruning edit relation columns per-rule and can desync a
            // back-edge application from its declaration (the sort-only arity
            // fixup cannot re-permute). If canonicalization fails to restore a
            // sort-consistent VC, we emit this snapshot (un-optimized but
            // well-formed) rather than an ill-sorted program AY would reject.
            let mut pre_opt_snapshot = chc_vc.clone();
            super::chc::report_slot_layout(&chc_vc, "00_pre_opt");
            run_emit_time_chc_passes(&mut chc_vc, const_prop_disabled);
            // Lost-checks recovery (#67 shape), the FALLBACK path. When const-prop,
            // false-rule elimination and orphan pruning erase the LAST error
            // obligation of a VC with registered properties, nothing was proved: the
            // checks may be dead, folded, or never reached by a broken encoding, and
            // all three look the same afterwards (the straight-line discharge below
            // refuses the shape, and the driver reports it INCONCLUSIVE). Re-run the
            // passes over the pre-optimization VC with the error obligations kept, so
            // the discharge and the solver decide them.
            //
            // FIRST CHOICE is the out-of-band record, not this: a check whose guard
            // folds to `false` is marked `discharged_at_encode` by
            // `eliminate_trivially_false_rules` (which const-prop runs inside the
            // passes above), and the gate further down turns a fully accounted VC
            // into the canonical `false => error` obligation with no solver run.
            // `passes_lost_every_error_obligation` therefore exempts a VC whose every
            // property carries that reason, and this fallback takes only what is left:
            // an obligation NOBODY accounted for (an orphaned block relation, an
            // aggregate `error` edge, or a mix where one property was marked and
            // another was pruned).
            if !super::chc::lost_obligation_recovery_disabled()
                && trust_mc_core::chc::passes_lost_every_error_obligation(
                    &pre_opt_snapshot,
                    &chc_vc,
                )
            {
                tracing::warn!(
                    properties = chc_vc.properties.len(),
                    "CHC: emit-time passes erased every error obligation of a VC with registered \
                     properties; re-running them with error obligations kept"
                );
                pre_opt_snapshot.keep_error_obligations = true;
                chc_vc = pre_opt_snapshot.clone();
                run_emit_time_chc_passes(&mut chc_vc, const_prop_disabled);
            }

            // SOUNDNESS fail-close: slot MISALIGNMENT must be caught HERE, before
            // anything reasons about the VC. The canonicalizer only rewrites
            // applications that fail the SORT check, so a permutation inside a run
            // of identically-sorted columns survives it untouched: every app still
            // sort-conforms while binding a different state variable at the same
            // position. The frame is then corrupt, a block's own body constraints
            // contradict each other, its successor is unreachable, and the error
            // edge cannot be derived — the query returns UNSAT and a FALSE
            // assertion is reported PROVEN, with no marker anywhere.
            //
            // This cannot be deferred to the existing net further down: the
            // straightline discharge below replaces every rule with
            // `(=> false error)`, so by then there is no misalignment left to see
            // and the collapsed VC looks perfectly healthy. Confirmed live on
            // `assert!(it.next().is_none())` over a 3-element slice, where both
            // that assertion and its negation verified SUCCESSFUL.
            if !super::chc::block_relation_slot_names_consistent(&chc_vc) {
                tracing::warn!(
                    "CHC: relation applications are slot-MISALIGNED (sorts agree, slot \
                     identities do not); emitting pre-optimization VC to preserve soundness"
                );
                chc_vc = pre_opt_snapshot.clone();
                super::chc::fixup_relation_app_arities(&mut chc_vc);
            }

            let false_rules = chc_vc.eliminate_trivially_false_rules();
            if false_rules > 0 {
                tracing::debug!(
                    false_rules,
                    "CHC: eliminated constant-false rules before emission"
                );
            }
            // SOUNDNESS fail-close (#67; live probe: fail_missing_recursion_attr
            // at the v24 gate): the translate-level degenerate check passes a
            // healthy system that THIS emit-time pipeline (const-prop ->
            // trivially-false elimination -> orphan prune) can still collapse
            // to zero program rules while per-property relations stay
            // registered. Rule-less registered properties auto-report SUCCESS
            // — demote (bump the per-fn chc_fallback count, keyed by the block
            // relation prefix) so any PROOF verdict becomes FAILURE. VCs whose
            // rules were LEGITIMATELY cleared by a discharge (TIC,
            // straightline) carry `trivially_safe_discharged` and are exempt.
            // Every obligation discharged at encode time: emit the CANONICAL
            // discharge so the driver can see it, instead of leaving an absence
            // it must read as a lost check.
            //
            // A registered property with no rule is ambiguous — "the encoder
            // proved it cannot fire" and "the encoder dropped it" look
            // identical — so the driver fails closed with
            // `[AY:UNKNOWN_REASON:LostErrorRules]`. Measured 2026-09-17: that
            // was 32 of 32 unparked CHC `unknown` rows, and the driver is right
            // to refuse. The cure is to stop producing the ambiguity.
            //
            // `all_properties_discharged_at_encode` is the soundness gate: at
            // least one property, EVERY one carrying a reason, and no
            // `error_p{id}`-headed rule surviving. A check whose rule was
            // deleted downstream was never marked, so the test fails and this
            // does nothing.
            //
            // `replace_with_unsat_error_obligation` is the same shape TIC and
            // the straight-line proof already emit, and the same one
            // `eliminate_trivially_false_rules` deliberately RETAINS (a literal
            // `false` body with no body relation). The driver recognises it via
            // `smt_error_query_has_false_error_obligation` and reports a clean
            // proof WITHOUT running a solver — so, unlike the in-band marker
            // this replaces (reverted in 0b89f4734 after it cost five real
            // proofs and a 1.8x slowdown), it costs the solver nothing.
            if chc_vc.all_properties_discharged_at_encode() {
                let reasons: std::collections::BTreeSet<&str> =
                    chc_vc.properties.iter().filter_map(|p| p.discharged_at_encode).collect();
                tracing::debug!(
                    properties = chc_vc.properties.len(),
                    ?reasons,
                    "CHC: every obligation discharged at encode time; emitting the canonical \
                     `false => error` obligation"
                );
                super::chc::straightline_proof::replace_with_unsat_error_obligation(&mut chc_vc);
                chc_vc.trivially_safe_discharged = true;
            }

            if !chc_vc.trivially_safe_discharged && !chc_vc.properties.is_empty() {
                let has_program_rule = chc_vc.rules.iter().any(|r| {
                    let head: &str = r.head.name.as_ref();
                    head != "error" && !head.starts_with("error_p")
                });
                // A deliberate-fail VC (e.g. the loop-decreases ranking lane in
                // codegen_function.rs) is an unconditional `error_pN` FACT plus
                // its bridge — FAILURE is guaranteed by construction, so the
                // auto-SUCCESS hazard this guard closes cannot occur. Exempt the
                // shape: demoting it only taints an already-fail-closed verdict.
                let has_unconditional_error_fact = chc_vc.rules.iter().any(|r| {
                    let head: &str = r.head.name.as_ref();
                    head.starts_with("error_p")
                        && r.body.relation.is_none()
                        && r.body.constraints.is_empty()
                });
                if !has_program_rule && !has_unconditional_error_fact {
                    let fn_name = chc_vc
                        .relations
                        .iter()
                        .find_map(|rel| {
                            let name: &str = rel.name.as_ref();
                            name.split_once("__bb").map(|(f, _)| f.to_string())
                        })
                        .unwrap_or_else(|| "unknown".to_string());
                    tracing::warn!(
                        fn_name = %fn_name,
                        properties = chc_vc.properties.len(),
                        "CHC: degenerate system after emit-time optimization — registered properties but no program rules; demoting (fail-closed)"
                    );
                    let cur = super::chc::get_chc_fallback_count_for_fn(&fn_name);
                    super::chc::set_chc_fallback_count_for_fn(&fn_name, cur + 1);
                }
            }
            if self.config.chc_straightline_discharge
                && super::chc::discharge_straightline_safety(&mut chc_vc)
            {
                tracing::debug!("CHC: bounded straight-line proof discharged scalarized VC");
            }

            // Part of #argorder: final safety net. If the optimization +
            // canonicalization pipeline still left any block-relation
            // application sort-inconsistent with its declaration, AY's CHC
            // parser would reject the whole program (UNKNOWN, mis-mapped to
            // FAILED). The pre-optimization snapshot is well-formed by
            // construction (it is the direct, arity-fixed output of
            // `translate`), so emit it instead — correctness over the arity
            // reduction the optimizations would have provided.
            // The sort check catches applications AY's parser would reject. It
            // cannot catch a permutation inside a run of identically-sorted
            // columns, which is strictly worse than a rejection: the frame is
            // silently misaligned, a block's own body constraints become
            // contradictory, its successor turns unreachable, and the error edge
            // is then underivable — a FALSE assertion is reported proven, with no
            // fallback marker, no demotion and nothing in the CTREX breakdown.
            // Confirmed live on `assert!(it.next().is_none())` over a 3-element
            // slice. Slot identity is checked by name, and a disagreement is
            // treated exactly like a sort disagreement: discard the optimized VC.
            if !super::chc::block_relation_apps_consistent(&chc_vc) {
                tracing::warn!(
                    "CHC: optimization pipeline produced sort-inconsistent relation \
                     applications; emitting pre-optimization VC to preserve soundness"
                );
                chc_vc = pre_opt_snapshot;
            } else if !super::chc::block_relation_slot_names_consistent(&chc_vc) {
                tracing::warn!(
                    "CHC: optimization pipeline produced slot-MISALIGNED relation \
                     applications (sorts agree, slot identities do not); emitting \
                     pre-optimization VC to preserve soundness"
                );
                chc_vc = pre_opt_snapshot;
            }

            // LAST: project unconstrained relation arguments when AY's executor
            // admission would otherwise reject the emitted problem outright
            // (`ChcParseError`, no solver run). Runs after the discharge and
            // the consistency nets above and re-checks them itself; see
            // `chc::admission_prune`.
            super::chc::prune_unconstrained_relation_args_for_admission(&mut chc_vc);

            // After every pass that can drop a sort's last user: keep only the
            // datatype declarations the emitted problem reaches. Exact; the
            // `TRUST_MC_CHC_PRUNE_DATATYPES=off` lever exists for A/B measurement.
            if std::env::var("TRUST_MC_CHC_PRUNE_DATATYPES").as_deref() != Ok("off") {
                let dropped = chc_vc.prune_unreachable_datatype_decls();
                if dropped > 0 {
                    tracing::debug!("CHC: pruned {dropped} unreachable datatype declarations");
                }
            }

            // Last of all, so no pass substitutes the definitions back: name the
            // links of a bitvector `ite` chain too deep for AY to decide quickly
            // (the inline walker's replay of a loop to a caller's bound). Exact;
            // `TRUST_MC_CHC_NAME_ITE_CHAINS=off` is the A/B lever. See
            // trust-mc-core `chc_optimize_ite_chains.rs`.
            let named = chc_vc.name_deep_ite_chains();
            if named > 0 {
                tracing::debug!("CHC: named {named} links of deep bitvector ite chains");
            }

            emit_chc(&chc_vc)
        } else {
            tracing::warn!(
                "split_emit_chc called but chc_vc is None - CHC codegen not performed; \
                 returning empty HORN program"
            );
            AYProgram::horn()
        };
        (MinimalAYCtx { unsupported_constructs: self.unsupported_constructs }, program)
    }
}

// Re-export test helpers for use by other test modules in the crate.
#[cfg(test)]
pub(in crate::codegen_ay) use testing::{
    with_test_ay_ctx, with_test_ay_ctx_for_source, with_test_ay_ctx_for_source_with_edition,
    with_test_ay_ctx_for_source_with_rustc_flags,
};

#[cfg(test)]
mod tests;

/// Existing guards against reducing a reachable safety/contract obligation.
pub(in crate::codegen_ay) fn chc_requires_unreduced_obligations(
    vc: &trust_mc_core::chc::ChcVc,
    is_contract_proof: bool,
) -> bool {
    trust_mc_core::chc_const_prop::has_scalarized_obj_valid_liveness(vc)
        || trust_mc_core::chc_const_prop::has_scalarized_obj_size_bounds(vc)
        || trust_mc_core::chc_const_prop::has_signed_overflow_error_edge(vc)
        || (is_contract_proof && !trust_mc_core::chc_const_prop::has_block_relation_cycle(vc))
}

/// The emit-time optimization passes (const-prop, orphan prune, dead scalars,
/// scalarization, dead constraints, arity fixup, canonicalization), factored out
/// of `split_emit` so the lost-checks recovery can re-run them over the
/// pre-optimization VC in keep-error-obligations mode.
pub(in crate::codegen_ay) fn run_emit_time_chc_passes(
    chc_vc: &mut trust_mc_core::chc::ChcVc,
    const_prop_disabled: bool,
) {
    if !const_prop_disabled {
        let propagated = chc_vc.propagate_constants();
        if propagated > 0 {
            tracing::debug!(propagated, "CHC: propagated constant relation arguments (#3371)");
        }
        // Part of #3793: Constant propagation may eliminate rules
        // (via eliminate_trivially_false_rules), creating new orphan
        // blocks whose body relations are no longer targeted as heads.
        // Prune these to prevent PDR from freely instantiating them.
        chc_vc.prune_orphan_block_rules();

        // Second-pass dead scalar elimination: after const_prop +
        // trivially-false rule elimination + orphan pruning, scalars
        // that were previously live (constrained in now-eliminated
        // rules) may become pure identity passthroughs.
        let pruned = chc_vc.prune_dead_identity_scalars();
        if pruned > 0 {
            tracing::debug!(pruned, "CHC: post-constprop dead scalar pruning");
        }
    }

    // Normalize free-variable array bases: the encoder creates
    // `__chc_array_N` free vars as store chain bases for local
    // array initialization (e.g., `let arr = [1,2,3,4]`).
    // Replace these with `const_array(...)` so the scalarizer
    // can decompose the store chains into per-index scalars.
    let normalized = chc_vc.normalize_free_array_bases();
    if normalized > 0 {
        tracing::debug!(normalized, "CHC: normalized free-var array bases to const_array");
    }

    // Second-pass scalarization: after constant propagation
    // resolves array indices to constants and dead-identity
    // pruning removes passthrough arrays, run the scalarizer
    // again. Arrays that were non-scalarizable before (symbolic
    // indices or ≥2 surviving arrays blocking each other) may
    // now qualify. Also re-runs const-folding and dead-scalar
    // pruning internally.
    super::translation_deadline::check_now("chc_emit_optimize");
    super::chc::scalarize_vc(chc_vc);
    super::translation_deadline::check_now("chc_emit_optimize");
    super::chc::report_slot_layout(chc_vc, "02_scalarize");

    // Strip dead constraints that reference only universally
    // quantified free variables (not in any relation's args).
    // Also prune stale declare-var entries. Array-sorted vars
    // removed from relations by prune_vc_unused_type_arrays
    // leave behind store constraints that force the solver
    // into Array theory unnecessarily.
    let dead_stripped = chc_vc.prune_dead_vars_and_constraints();
    if dead_stripped > 0 {
        tracing::debug!(dead_stripped, "CHC: dead constraint/var pruning");
    }

    // Part of #4286: later CHC optimization passes can leave embedded
    // relation FuncApps with stale arity in constraints even after the
    // relation declarations were rewritten. Repair the final VC just
    // before emission so the emitted HORN program matches its decls.
    super::chc::fixup_relation_app_arities(chc_vc);
    super::chc::report_slot_layout(chc_vc, "04_fixup_arities");
    super::chc::prune_dead_array_relation_args(chc_vc);
    // Part of #argorder: the passes above can leave a relation
    // application mis-permuted relative to its declaration (a column
    // run of identical sorts defeats the sort-only arity fixup).
    // Re-permute divergent applications by slot name, then re-run the
    // arity fixup as the downstream safety net.
    super::chc::canonicalize_block_relation_apps(chc_vc);
    super::chc::report_slot_layout(chc_vc, "05_canonicalize");
    super::chc::fixup_relation_app_arities(chc_vc);
}
