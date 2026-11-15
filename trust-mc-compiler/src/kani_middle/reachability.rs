// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This module implements a cross-crate collector that allow us to find all items that
//! should be included in order to verify one or more proof harness.
//!
//! This module works as following:
//!   - Traverse all reachable items starting at the given starting points.
//!   - For every function, traverse its body and collect the following:
//!     - Constants / Static objects.
//!     - Functions that are called or have their address taken.
//!     - VTable methods for types that are coerced as unsized types.
//!   - For every static, collect initializer and drop functions.
//!
//! We have kept this module agnostic of any Kani code in case we can contribute this back to rustc.
//!
//! Note that this is a copy of `reachability.rs` that uses rustc_public but the public APIs are still
//! kept with internal APIs.
use tracing::{debug, debug_span, trace};

use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::fx::FxHashSet;
#[cfg(trust_toolchain)]
use rustc_data_structures::stable_hash::{StableHash, StableHasher};
#[cfg(not(trust_toolchain))]
use rustc_data_structures::stable_hasher::{HashStable, StableHasher};
use rustc_middle::ty::{TyCtxt, VtblEntry};
use rustc_public::CrateItem;
use rustc_public::mir::alloc::{AllocId, GlobalAlloc};
use rustc_public::mir::mono::{Instance, InstanceKind, MonoItem, StaticDef};
use rustc_public::mir::{
    Body, CastKind, ConstOperand, MirVisitor, PointerCoercion, Rvalue, Terminator, TerminatorKind,
    visit::Location,
};
use rustc_public::rustc_internal;
use rustc_public::ty::{Allocation, ClosureKind, ConstantKind, RigidTy, Ty, TyKind};
use rustc_public::{CrateDef, ItemKind};
#[cfg(debug_assertions)]
use rustc_session::config::OutputType;
use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};
use std::sync::{Mutex, OnceLock};
#[cfg(debug_assertions)]
use std::{
    fs::File,
    io::{BufWriter, Write},
};

use crate::kani_middle::coercion;
use crate::kani_middle::coercion::CoercionBase;
use crate::kani_middle::is_anon_static;
use crate::kani_middle::std_abstraction::{Abstraction, StdAbstraction};
use crate::kani_middle::transform::BodyTransformation;

pub(crate) trait AbstractionBoundary {
    fn has_explicit_stub(&self, path: &str) -> bool;
    /// Returns `true` if the path is backed by a CHC handler (e.g., stable atomic
    /// operations) even without an explicit stub in `StubRegistry`. (Part of #3777)
    fn has_handler_backed_abstraction(&self, path: &str) -> bool;
    fn record_unstubbed_abstraction(&self, path: &str);
    fn begin_inventory(&self) {}
    fn finish_inventory(&self) {}
    fn record_reachable_body(&self, _caller: Instance, _body: &Body) {}
    /// A direct call observed by this collector, not a path-based approximation.
    fn record_unstubbed_call(
        &self,
        path: &str,
        _callee: Instance,
        _site: Option<AbstractionCallsite<'_>>,
        _identity_established: bool,
    ) {
        self.record_unstubbed_abstraction(path);
    }
}

/// Compiler-owned custody of a direct call in a reachable body.
#[derive(Clone, Copy)]
pub(crate) struct AbstractionCallsite<'a> {
    pub caller: Instance,
    pub body: &'a Body,
    pub block: usize,
}

/// Where reachability stops: the backend's stubs, the standard-library
/// abstraction set, and the unit's harness stub map, consulted first.
///
/// `#[kani::stub(std::fs::read, mock_read)]` makes `FnStubPass` hand reachability
/// `mock_read`'s body for `std::fs::read`. Deciding by `std::fs` before the stub map
/// was consulted abstracted the call anyway: `mock_read` was never collected, the
/// call stayed an unconstrained `fs` pre-route, and the harness checked a different
/// program than the one Kani checks.
struct Boundary<'a> {
    backend: &'a dyn AbstractionBoundary,
    stubs: crate::kani_middle::codegen_units::Stubs,
    std: StdAbstraction,
}

/// Whether `FnStubPass` replaces `instance`'s body under `stubs`.
///
/// Mirrors that pass's own filter: only a `from -> to` pair where BOTH sides have a body is
/// a body replacement. Every call site naming a stubbed function is rewritten to the stub by
/// `CallSiteStubPass`, so an extern original is never reached through this instance and the
/// boundary keeps deciding it.
pub(crate) fn harness_stub_replaces_body(
    stubs: &crate::kani_middle::codegen_units::Stubs,
    instance: Instance,
) -> bool {
    let TyKind::RigidTy(RigidTy::FnDef(from, _)) = instance.ty().kind() else {
        return false;
    };
    stubs.get(&from).is_some_and(|to| from.body().is_some() && to.body().is_some())
}

/// Collect all reachable items starting from the given starting points.
pub(crate) fn collect_reachable_items(
    tcx: TyCtxt,
    transformer: &mut BodyTransformation,
    starting_points: &[MonoItem],
    abstraction_boundary: &dyn AbstractionBoundary,
) -> (Vec<MonoItem>, CallGraph) {
    abstraction_boundary.begin_inventory();
    // For each harness, collect items using the same collector.
    // I.e.: This will return any item that is reachable from one or more of the starting points.
    let boundary = Boundary {
        backend: abstraction_boundary,
        stubs: transformer.stub_map_for_walk(),
        std: StdAbstraction::resolve(tcx),
    };
    let mut collector = MonoItemsCollector::new(tcx, transformer, &boundary);
    crate::kani_middle::dyn_universe::begin_collection();
    for item in starting_points {
        collector.collect(item);
    }
    collector.call_graph.dyn_universe = crate::kani_middle::dyn_universe::end_collection();
    // Design 5 backstop (`loop_contract_reach.rs`): which reachable functions
    // can reach a loop contract, for the CHC harness-body prescan.
    let loop_contract_reach =
        collector.call_graph.loop_contract_reach(&collector.collected, &collector.opaque);
    collector.call_graph.dyn_universe.set_loop_contract_reach(loop_contract_reach);

    #[cfg(debug_assertions)]
    collector
        .call_graph
        .dump_dot(tcx, starting_points.first().cloned())
        .unwrap_or_else(|e| tracing::error!("Failed to dump call graph: {e}"));

    tcx.dcx().abort_if_errors();

    // Part of #1670: Log collection statistics for verification.
    // Success criteria: No internal BTree functions (NodeRef, search_tree, etc.) collected.
    // Verified: 22 total functions (infrastructure), 0 internal BTree functions.
    let fn_count = collector.collected.iter().filter(|i| matches!(i, MonoItem::Fn(_))).count();
    let abstracted_count = collector.abstracted.len();
    debug!(
        fn_count,
        abstracted_count,
        "Reachability: collected {} functions, abstracted {} at stub boundary",
        fn_count,
        abstracted_count
    );

    // Sort the result so code generation follows deterministic order.
    // This helps us to debug the code, but it also provides the user a good experience since the
    // order of the errors and warnings is stable.
    let mut sorted_items: Vec<_> = collector.collected.into_iter().collect();
    sorted_items.sort_by_cached_key(|item| to_fingerprint(tcx, item));
    abstraction_boundary.finish_inventory();
    (sorted_items, collector.call_graph)
}

/// Collect all (top-level) items in the crate that matches the given predicate.
/// An item can only be a root if they are a non-generic function.
pub(crate) fn filter_crate_items<F>(tcx: TyCtxt, predicate: F) -> Vec<Instance>
where
    F: Fn(TyCtxt, Instance) -> bool,
{
    let crate_items = rustc_public::all_local_items();
    // Filter regular items.
    crate_items
        .iter()
        .filter_map(|item| {
            // Only collect monomorphic items.
            matches!(item.kind(), ItemKind::Fn)
                .then(|| {
                    Instance::try_from(*item)
                        .ok()
                        .and_then(|instance| predicate(tcx, instance).then_some(instance))
                })
                .flatten()
        })
        .collect::<Vec<_>>()
}

/// Reason for introducing an edge in the call graph.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
enum CollectionReason {
    DirectCall,
    IndirectCall,
    VTableMethod,
    Static,
    StaticDrop,
}

/// A destination of the edge in the call graph.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct CollectedItem {
    item: MonoItem,
    reason: CollectionReason,
}

struct MonoItemsCollector<'tcx, 'a> {
    /// The compiler context.
    tcx: TyCtxt<'tcx>,
    /// The body transformation object used to retrieve a transformed body.
    transformer: &'a mut BodyTransformation,
    /// Set of collected items used to avoid entering recursion loops.
    collected: FxHashSet<MonoItem>,
    /// Functions that were abstracted at the reachability boundary.
    abstracted: FxHashSet<MonoItem>,
    /// Visited functions whose body calls (or has a vtable method that is) a
    /// function abstracted at the boundary, whose body was never followed
    /// (design 5, `loop_contract_reach.rs`).
    opaque: FxHashSet<MonoItem>,
    /// Items enqueued for visiting.
    queue: Vec<MonoItem>,
    /// Call graph used for dataflow analysis.
    call_graph: CallGraph,
    /// Where reachability stops.
    boundary: &'a Boundary<'a>,
}

impl<'tcx, 'a> MonoItemsCollector<'tcx, 'a> {
    fn new(
        tcx: TyCtxt<'tcx>,
        transformer: &'a mut BodyTransformation,
        boundary: &'a Boundary<'a>,
    ) -> Self {
        MonoItemsCollector {
            tcx,
            collected: FxHashSet::default(),
            abstracted: FxHashSet::default(),
            opaque: FxHashSet::default(),
            queue: vec![],
            call_graph: CallGraph::default(),
            transformer,
            boundary,
        }
    }

    /// Collects all reachable items starting from the given root.
    fn collect(&mut self, root: &MonoItem) {
        debug!(?root, "collect");
        self.queue.push(root.clone());
        self.reachable_items();
    }

    /// Traverses the call graph starting from the given root. For every function, we visit all
    /// instruction looking for the items that should be included in the compilation.
    fn reachable_items(&mut self) {
        while let Some(to_visit) = self.queue.pop() {
            if self.abstracted.contains(&to_visit) {
                continue;
            }
            if matches!(
                &to_visit,
                MonoItem::Fn(instance) if self.boundary.abstracts(self.tcx, *instance)
            ) {
                trace!(?to_visit, "reachable_items: abstract stub boundary");
                self.abstracted.insert(to_visit);
                continue;
            }
            if !self.collected.contains(&to_visit) {
                let next_items = match &to_visit {
                    MonoItem::Fn(instance) => self.visit_fn(*instance),
                    MonoItem::Static(static_def) => self.visit_static(*static_def),
                    MonoItem::GlobalAsm(_) => {
                        self.visit_asm(&to_visit);
                        vec![]
                    }
                };
                self.call_graph.add_edges(&to_visit, &next_items);

                self.queue.extend(next_items.into_iter().filter_map(
                    |CollectedItem { item, .. }| {
                        (!self.collected.contains(&item) && !self.abstracted.contains(&item))
                            .then_some(item)
                    },
                ));
                self.collected.insert(to_visit);
            }
        }
    }

    /// Visit a function and collect all mono-items reachable from its instructions.
    fn visit_fn(&mut self, instance: Instance) -> Vec<CollectedItem> {
        let _guard = debug_span!("visit_fn", function=?instance).entered();
        if self.boundary.abstracts(self.tcx, instance) {
            trace!(?instance, "visit_fn: abstract stub boundary");
            return vec![];
        }
        let body = self.transformer.body_ref(self.tcx, instance);
        self.boundary.backend.record_reachable_body(instance, body);
        let mut collector = MonoItemsFnCollector {
            tcx: self.tcx,
            collected: FxHashSet::default(),
            boundary: self.boundary,
            body,
            caller: instance,
            terminator_blocks: body
                .blocks
                .iter()
                .enumerate()
                .map(|(bb, block)| (&block.terminator as *const Terminator as usize, bb))
                .collect(),
            calls_abstract: false,
        };
        collector.visit_body(body);
        if collector.calls_abstract {
            self.opaque.insert(MonoItem::Fn(instance));
        }
        collector.collected.into_iter().collect()
    }

    /// Visit a static object and collect drop / initialization functions.
    fn visit_static(&mut self, def: StaticDef) -> Vec<CollectedItem> {
        let _guard = debug_span!("visit_static", ?def).entered();
        let mut next_items = vec![];

        // Collect drop function, unless it's an anonymous static.
        if !is_anon_static(self.tcx, def.def_id()) {
            let static_ty = def.ty();
            let instance = Instance::resolve_drop_in_place(static_ty);
            next_items.push(CollectedItem {
                item: instance.into(),
                reason: CollectionReason::StaticDrop,
            });

            // Collect initialization. A foreign (`extern "C"`) static has no
            // MIR initializer body — `eval_initializer()` would span_bug/panic
            // (which `.expect()` cannot survive). Foreign statics contribute no
            // initializer allocation items, so skipping them is exhaustive.
            if !self.tcx.is_foreign_item(rustc_internal::internal(self.tcx, def.def_id())) {
                let alloc = def.eval_initializer().expect("static initializer");
                debug!(?alloc, "visit_static: initializer");
                for (_, prov) in alloc.provenance.ptrs {
                    next_items.extend(
                        collect_alloc_items(self.tcx, prov.0, self.boundary)
                            .into_iter()
                            .map(|item| CollectedItem { item, reason: CollectionReason::Static }),
                    );
                }
            }
        }

        next_items
    }

    /// Visit global assembly and collect its item.
    fn visit_asm(&mut self, item: &MonoItem) {
        debug!(?item, "visit_asm");
    }
}

struct MonoItemsFnCollector<'collector, 'body, 'tcx> {
    tcx: TyCtxt<'tcx>,
    collected: FxHashSet<CollectedItem>,
    boundary: &'collector Boundary<'collector>,
    body: &'body Body,
    caller: Instance,
    terminator_blocks: HashMap<usize, usize>,
    /// The body names a function abstracted at the boundary (a call, a drop,
    /// a reification or a vtable method), which is never collected.
    calls_abstract: bool,
}

impl MonoItemsFnCollector<'_, '_, '_> {
    /// Collect the implementation of all trait methods and its supertrait methods for the given
    /// concrete type.
    fn collect_vtable_methods(&mut self, concrete_ty: Ty, trait_ty: Ty) {
        trace!(?concrete_ty, ?trait_ty, "collect_vtable_methods");
        let concrete_kind = concrete_ty.kind();
        let trait_kind = trait_ty.kind();

        assert!(!concrete_kind.is_trait(), "expected a concrete type, but found `{concrete_ty:?}`");
        assert!(trait_kind.is_trait(), "expected a trait `{trait_ty:?}`");
        if let Some(principal) = trait_kind.trait_principal() {
            // A trait object type can have multiple trait bounds but up to one non-auto-trait
            // bound. This non-auto-trait, named principal, is the only one that can have methods.
            // https://doc.rust-lang.org/reference/special-types-and-traits.html#auto-traits
            let trait_ref = rustc_internal::internal(self.tcx, principal.with_self_ty(concrete_ty));
            let trait_ref = self.tcx.instantiate_bound_regions_with_erased(trait_ref);

            // Walk all methods of the trait, including those of its supertraits
            let entries = self.tcx.vtable_entries(trait_ref);
            let methods = entries
                .iter()
                .filter_map(|entry| match entry {
                    VtblEntry::MetadataAlign
                    | VtblEntry::MetadataDropInPlace
                    | VtblEntry::MetadataSize
                    | VtblEntry::Vacant => None,
                    VtblEntry::TraitVPtr(_) => {
                        // all super trait items already covered, so skip them.
                        None
                    }
                    VtblEntry::Method(instance) => {
                        let instance = rustc_internal::stable(instance);
                        if !should_codegen_locally(&instance) {
                            return None;
                        }
                        if self.boundary.abstracts(self.tcx, instance) {
                            self.calls_abstract = true;
                            return None;
                        }
                        Some(MonoItem::Fn(instance))
                    }
                })
                .collect::<Vec<_>>();
            trace!(methods=?methods, "collect_vtable_methods");
            self.collected.extend(
                methods
                    .into_iter()
                    .map(|item| CollectedItem { item, reason: CollectionReason::VTableMethod }),
            );
        }

        // Add the destructor for the concrete type.
        let instance = Instance::resolve_drop_in_place(concrete_ty);
        self.collect_instance(instance, false);
    }

    /// Collect an instance depending on how it is used (invoked directly or via fn_ptr).
    fn collect_instance(&mut self, instance: Instance, is_direct_call: bool) {
        self.collect_instance_at(instance, is_direct_call, None);
    }

    fn collect_instance_at(
        &mut self,
        instance: Instance,
        is_direct_call: bool,
        terminator: Option<&Terminator>,
    ) {
        if self.boundary.abstracts_at(self.tcx, instance, || {
            let terminator = terminator?;
            self.terminator_blocks
                .get(&(terminator as *const Terminator as usize))
                .copied()
                .map(|block| AbstractionCallsite { caller: self.caller, body: self.body, block })
        }) {
            trace!(?instance, "collect_instance: abstract stub boundary");
            self.calls_abstract = true;
            return;
        }
        let should_collect = match instance.kind {
            #[cfg(all(trust_toolchain, version("1.101")))]
            InstanceKind::LlvmIntrinsic => self.tcx.dcx().fatal(format!(
                "trust-mc cannot verify LLVM intrinsic `{}`: no Rust fallback body or \
                 verification encoding is available",
                instance.name(),
            )),
            InstanceKind::Virtual { .. } => {
                // Instance definition has no body.
                assert!(is_direct_call, "Expected direct call {instance:?}");
                false
            }
            InstanceKind::Intrinsic => {
                // Intrinsics may have a fallback body.
                assert!(is_direct_call, "Expected direct call {instance:?}");
                let TyKind::RigidTy(RigidTy::FnDef(def, _)) = instance.ty().kind() else {
                    unreachable!("Expected function type for intrinsic: {instance:?}")
                };
                // The compiler is currently transitioning how to handle intrinsic fallback body.
                // Until https://github.com/rust-lang/project-stable-mir/issues/79 is implemented
                // we have to check `must_be_overridden` and `has_body`.
                !def.as_intrinsic().expect("intrinsic def").must_be_overridden()
                    && instance.has_body()
            }
            InstanceKind::Shim | InstanceKind::Item => true,
        };
        if should_collect && should_codegen_locally(&instance) {
            trace!(?instance, "collect_instance");
            let reason = if is_direct_call {
                CollectionReason::DirectCall
            } else {
                CollectionReason::IndirectCall
            };
            self.collected.insert(CollectedItem { item: instance.into(), reason });
        }
    }

    /// Collect constant values represented by static variables.
    fn collect_allocation(&mut self, alloc: &Allocation) {
        debug!(?alloc, "collect_allocation");
        for (_, id) in &alloc.provenance.ptrs {
            self.collected.extend(
                collect_alloc_items(self.tcx, id.0, self.boundary)
                    .into_iter()
                    .map(|item| CollectedItem { item, reason: CollectionReason::Static }),
            );
        }
    }
}

/// Visit every instruction in a function and collect the following:
/// 1. Every function / method / closures that may be directly invoked.
/// 2. Every function / method / closures that may have their address taken.
/// 3. Every method that compose the impl of a trait for a given type when there's a conversion
///    from the type to the trait.
///    - I.e.: If we visit the following code:
///      ```
///      let var = MyType::new();
///      let ptr : &dyn MyTrait = &var;
///      ```
///      We collect the entire implementation of `MyTrait` for `MyType`.
/// 4. Every Static variable that is referenced in the function or constant used in the function.
/// 5. Drop glue.
/// 6. Static Initialization
///
/// Remark: This code has been mostly taken from `rustc_monomorphize::collector::MirNeighborCollector`.
impl MirVisitor for MonoItemsFnCollector<'_, '_, '_> {
    /// Collect the following:
    /// - Trait implementations when casting from concrete to dyn Trait.
    /// - Functions / Closures that have their address taken.
    /// - Thread Local.
    fn visit_rvalue(&mut self, rvalue: &Rvalue, location: Location) {
        trace!(rvalue=?*rvalue, "visit_rvalue");

        match *rvalue {
            Rvalue::Cast(
                CastKind::PointerCoercion(PointerCoercion::Unsize),
                ref operand,
                target,
            ) => {
                // Check if the conversion include casting a concrete type to a trait type.
                // If so, collect items from the impl `Trait for Concrete {}`.
                let target_ty = target;
                let source_ty = operand.ty(self.body.locals()).expect("unsize operand type");
                let (src_ty, dst_ty) = extract_unsize_coercion(self.tcx, source_ty, target_ty);
                if !src_ty.kind().is_trait() && dst_ty.kind().is_trait() {
                    debug!(?src_ty, ?dst_ty, "collect_vtable_methods");
                    // Every runtime type a `dyn` receiver can have (design 3, D2).
                    crate::kani_middle::dyn_universe::note_coercion(
                        src_ty,
                        dst_ty.kind().trait_principal().as_ref(),
                    );
                    self.collect_vtable_methods(src_ty, dst_ty);
                } else if src_ty.kind().is_trait() && dst_ty.kind().is_trait() {
                    // A `dyn` -> `dyn` unsize (trait upcasting): the target's
                    // runtime types include the source's (design 3, D2).
                    crate::kani_middle::dyn_universe::note_dyn_to_dyn(
                        src_ty.kind().trait_principal().as_ref(),
                        dst_ty.kind().trait_principal().as_ref(),
                    );
                }
            }
            Rvalue::Cast(
                CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer { .. }),
                ref operand,
                target,
            ) => {
                let operand_ty = operand.ty(self.body.locals()).expect("reify operand type");
                // Every function a harness can call through a pointer (design 3).
                crate::kani_middle::dyn_universe::note_fn_ptr_reification(operand_ty, target);
                let fn_kind = operand_ty.kind();
                if let RigidTy::FnDef(fn_def, args) = fn_kind.rigid().expect("rigid fn type") {
                    let instance =
                        Instance::resolve_for_fn_ptr(*fn_def, args).expect("resolve fn ptr");
                    self.collect_instance(instance, false);
                } else {
                    unreachable!("Expected FnDef type, but got: {:?}", fn_kind);
                }
            }
            Rvalue::Cast(
                CastKind::PointerCoercion(PointerCoercion::ClosureFnPointer(_)),
                ref operand,
                target,
            ) => {
                let source_ty = operand.ty(self.body.locals()).expect("closure operand type");
                crate::kani_middle::dyn_universe::note_fn_ptr_reification(source_ty, target);
                match source_ty.kind().rigid().expect("rigid closure type") {
                    RigidTy::Closure(def_id, args) => {
                        let instance =
                            Instance::resolve_closure(*def_id, args, ClosureKind::FnOnce)
                                .expect("failed to normalize and resolve closure during codegen");
                        self.collect_instance(instance, false);
                    }
                    _ => unreachable!("Unexpected type: {:?}", source_ty), // external enum: RigidTy
                }
            }
            // A fn pointer a transmute produces may hold any value (design 3).
            Rvalue::Cast(CastKind::Transmute, _, target)
                if matches!(target.kind(), TyKind::RigidTy(RigidTy::FnPtr(..))) =>
            {
                crate::kani_middle::dyn_universe::note_fn_ptr_transmute(target);
            }
            Rvalue::ThreadLocalRef(item) => {
                trace!(?item, "visit_rvalue thread_local");
                let item =
                    MonoItem::Static(StaticDef::try_from(item).expect("thread local static def"));
                self.collected.insert(CollectedItem { item, reason: CollectionReason::Static });
            }
            _ => {} // external enum: Rvalue
        }

        self.super_rvalue(rvalue, location);
    }

    /// Collect constants that are represented as static variables.
    fn visit_const_operand(&mut self, constant: &ConstOperand, location: Location) {
        debug!(?constant, ?location, literal=?constant.const_, "visit_constant");
        let allocation = match constant.const_.kind() {
            ConstantKind::Allocated(allocation) => allocation,
            ConstantKind::Unevaluated(_) => {
                unreachable!("Instance with polymorphic constant: `{constant:?}`")
            }
            ConstantKind::Param(_) => unreachable!("Unexpected parameter constant: {constant:?}"),
            ConstantKind::ZeroSized => {
                // Nothing to do here.
                return;
            }
            ConstantKind::Ty(_) => {
                // Nothing to do here.
                return;
            }
        };
        self.collect_allocation(allocation);
    }

    /// Collect function calls.
    fn visit_terminator(&mut self, terminator: &Terminator, location: Location) {
        trace!(?terminator, ?location, "visit_terminator");

        match terminator.kind {
            TerminatorKind::Call { ref func, .. } => {
                let fn_ty = func.ty(self.body.locals()).expect("call func type");
                if let TyKind::RigidTy(RigidTy::FnDef(fn_def, args)) = fn_ty.kind() {
                    let instance = Instance::resolve(fn_def, &args).expect("resolve call instance");
                    self.collect_instance_at(instance, true, Some(terminator));
                } else if let TyKind::RigidTy(RigidTy::Closure(def_id, args)) = fn_ty.kind() {
                    // Direct closure-typed calls: emitted by the loop-contracts
                    // `decreases` instrumentation (measure closure evaluated at
                    // the loop head/latch). Resolve the Fn shim so the closure
                    // body is collected; FunctionInlinePass inlines the call at
                    // codegen (CallableKind::Closure).
                    let instance = Instance::resolve_closure(def_id, &args, ClosureKind::Fn)
                        .expect("failed to resolve direct closure call during reachability");
                    self.collect_instance(instance, true);
                } else {
                    assert!(
                        matches!(fn_ty.kind().rigid(), Some(RigidTy::FnPtr(..))),
                        "Unexpected type: {fn_ty:?}"
                    );
                }
            }
            TerminatorKind::Drop { ref place, .. } => {
                let place_ty = place.ty(self.body.locals()).expect("drop place type");
                let instance = Instance::resolve_drop_in_place(place_ty);
                self.collect_instance(instance, true);
            }
            TerminatorKind::InlineAsm { .. } => {
                // We don't support inline assembly. This shall be replaced by an unsupported
                // construct during codegen.
            }
            TerminatorKind::Abort | TerminatorKind::Assert { .. } => {
                // We generate code for this without invoking any lang item.
            }
            TerminatorKind::Goto { .. }
            | TerminatorKind::SwitchInt { .. }
            | TerminatorKind::Resume
            | TerminatorKind::Return
            | TerminatorKind::Unreachable => {}
        }

        self.super_terminator(terminator, location);
    }

    /// Collect any function definition that may occur as a type.
    ///
    /// The codegen stage will require the definition to be available.
    /// This is a conservative approach, since there are cases where the function is never
    /// actually used, so we don't need the body.
    ///
    /// Another alternative would be to lazily declare functions, but it would require a bigger
    /// change to codegen.
    fn visit_ty(&mut self, ty: &Ty, _: Location) {
        if let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind() {
            let instance = Instance::resolve(def, &args).expect("resolve fn def instance");
            self.collect_instance(instance, true);
        }
        self.super_ty(ty);
    }
}

fn extract_unsize_coercion(tcx: TyCtxt, orig_ty: Ty, dst_trait: Ty) -> (Ty, Ty) {
    let CoercionBase { src_ty, dst_ty } = coercion::extract_unsize_casting(
        tcx,
        rustc_internal::internal(tcx, orig_ty),
        rustc_internal::internal(tcx, dst_trait),
    );
    (rustc_internal::stable(src_ty), rustc_internal::stable(dst_ty))
}

/// Convert a `MonoItem` into a stable `Fingerprint` which can be used as a stable hash across
/// compilation sessions. This allow us to provide a stable deterministic order to codegen.
fn to_fingerprint(tcx: TyCtxt, item: &MonoItem) -> Fingerprint {
    tcx.with_stable_hashing_context(|mut hcx| {
        let mut hasher = StableHasher::new();
        #[cfg(not(trust_toolchain))]
        rustc_internal::internal(tcx, item).hash_stable(&mut hcx, &mut hasher);
        // Trust renamed `HashStable::hash_stable` to `StableHash::stable_hash`.
        #[cfg(trust_toolchain)]
        rustc_internal::internal(tcx, item).stable_hash(&mut hcx, &mut hasher);
        hasher.finish()
    })
}

/// Track functions that have already been warned about to avoid duplicate warnings.
/// Per designs/archive/2026-02-01-stub-coverage-validation.md: warning deduplication
static WARNED_UNSTUBBED_FUNCTIONS: OnceLock<Mutex<HashSet<String>>> = OnceLock::new();

impl Boundary<'_> {
    /// Is `instance`'s body behind the boundary, so that it is not collected?
    fn abstracts(&self, tcx: TyCtxt, instance: Instance) -> bool {
        self.abstracts_at(tcx, instance, || None)
    }

    fn abstracts_at<'a>(
        &self,
        tcx: TyCtxt,
        instance: Instance,
        site: impl FnOnce() -> Option<AbstractionCallsite<'a>>,
    ) -> bool {
        // The harness stub map decides first: a body `FnStubPass` replaces is the
        // user's stub, and the standard-library set must not hide it.
        if harness_stub_replaces_body(&self.stubs, instance) {
            trace!(?instance, "abstracts: harness stub replaces body -> collected");
            return false;
        }
        let def_id = rustc_internal::internal(tcx, instance.def.def_id());
        let path = tcx.def_path_str(def_id);

        let has_stub = self.backend.has_explicit_stub(&path);

        let abstraction = self.std.decide_definition(tcx, def_id);

        if abstraction.is_abstracted() {
            trace!(?path, ?abstraction, "abstracts: standard-library abstraction set");

            // Handler-backed abstractions (e.g., stable atomic ops) have CHC handlers
            // even without explicit stubs — no warning needed. (Part of #3777)
            let has_handler = self.backend.has_handler_backed_abstraction(&path);

            let unstubbed = !has_stub && !has_handler;
            // An item abstracted only by an anchor that failed closed on this
            // sysroot is recorded whatever the stub registry says: that its
            // stubs still describe the item is not established either (the
            // session's warning names the anchor).
            if unstubbed || abstraction == Abstraction::FailClosed {
                // Track unstubbed abstraction for summary (Part of #1685)
                self.backend.record_unstubbed_call(
                    &path,
                    instance,
                    site(),
                    abstraction != Abstraction::FailClosed,
                );
            }

            // Emit warning if abstracted without stub AND not handler-backed
            // Per designs/archive/2026-02-01-stub-coverage-validation.md
            if unstubbed {
                let warned_set =
                    WARNED_UNSTUBBED_FUNCTIONS.get_or_init(|| Mutex::new(HashSet::new()));
                let mut warned =
                    warned_set.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
                // Check contains first to avoid String allocation when already warned
                if !warned.contains(&path) {
                    tcx.dcx().warn(format!(
                        "Function `{}` is abstracted but has no stub; exact callsite modeling is checked during codegen.",
                        path
                    ));
                    warned.insert(path);
                }
            }
            return true;
        }

        // Fall back to exact stub matching for other stubbed functions
        has_stub
    }
}

/// Return whether we should include the item into codegen.
fn should_codegen_locally(instance: &Instance) -> bool {
    !instance.is_foreign_item()
}

fn collect_alloc_items(tcx: TyCtxt, alloc_id: AllocId, boundary: &Boundary<'_>) -> Vec<MonoItem> {
    trace!(?alloc_id, "collect_alloc_items");
    let mut items = vec![];
    match GlobalAlloc::from(alloc_id) {
        GlobalAlloc::Static(def) => {
            if is_anon_static(tcx, def.def_id()) {
                // Defensive: a foreign static has no initializer body and would
                // span_bug/panic here. Anonymous statics are never foreign, so
                // in practice this guard never fires — it only fails closed.
                if !tcx.is_foreign_item(rustc_internal::internal(tcx, def.def_id())) {
                    let alloc = def.eval_initializer().expect("anon static initializer");
                    items.extend(
                        alloc
                            .provenance
                            .ptrs
                            .iter()
                            .flat_map(|(_, prov)| collect_alloc_items(tcx, prov.0, boundary)),
                    );
                }
            } else {
                // This differ from rustc's collector since rustc does not include static from
                // upstream crates.
                let instance = Instance::try_from(CrateItem::from(def)).expect("static instance");
                should_codegen_locally(&instance).then(|| items.push(MonoItem::from(def)));
            }
        }
        GlobalAlloc::Function(instance) => {
            // A fn pointer in a constant or static value (design 3).
            crate::kani_middle::dyn_universe::note_fn_ptr_in_allocation();
            if should_codegen_locally(&instance) && !boundary.abstracts(tcx, instance) {
                items.push(MonoItem::from(instance));
            }
        }
        GlobalAlloc::Memory(alloc) => {
            items.extend(
                alloc
                    .provenance
                    .ptrs
                    .iter()
                    .flat_map(|(_, prov)| collect_alloc_items(tcx, prov.0, boundary)),
            );
        }
        vtable_alloc @ GlobalAlloc::VTable(..) => {
            // A vtable a constant or static holds creates `dyn` values of its
            // type without any `Unsize` in a body (design 3, D2).
            if let GlobalAlloc::VTable(concrete, principal) = &vtable_alloc {
                crate::kani_middle::dyn_universe::note_coercion(*concrete, principal.as_ref());
            }
            let vtable_id = vtable_alloc.vtable_allocation().expect("vtable allocation");
            items = crate::kani_middle::dyn_universe::inside_vtable(|| {
                collect_alloc_items(tcx, vtable_id, boundary)
            });
        }
        GlobalAlloc::TypeId { ty: _ } => {}
    }
    items
}

/// Call graph with edges annotated with the reason why they were added to the graph.
#[derive(Debug, Default)]
pub(crate) struct CallGraph {
    /// Every dyn coercion reachable from the starting points (design 3, D2:
    /// `dyn_universe.rs`).
    pub(crate) dyn_universe: crate::kani_middle::dyn_universe::DynUniverse,
    /// Nodes of the graph.
    nodes: HashSet<Node>,
    /// Edges of the graph.
    edges: HashMap<Node, Vec<CollectedNode>>,
    /// Since the graph is directed, we also store back edges.
    back_edges: HashMap<Node, Vec<CollectedNode>>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct Node(pub MonoItem);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct CollectedNode(pub CollectedItem);

impl CallGraph {
    /// Design 5 backstop (`loop_contract_reach.rs`): which functions have a
    /// path to a loop-contract register instance, which visited functions can
    /// reach no function the collector abstracted (`opaque` seeds the rest),
    /// and which functions are the target of an edge that is not a direct call
    /// (a fn-pointer reification, a vtable method, a pointer in an allocation).
    fn loop_contract_reach(
        &self,
        collected: &FxHashSet<MonoItem>,
        opaque: &FxHashSet<MonoItem>,
    ) -> crate::kani_middle::loop_contract_reach::LoopContractReach {
        use crate::kani_middle::loop_contract_reach::{LoopContractReach, is_register_instance};
        let registers = self
            .nodes
            .iter()
            .filter(
                |node| matches!(node.0, MonoItem::Fn(instance) if is_register_instance(instance)),
            )
            .map(|node| node.0.clone());
        let reaching = self.callers_closure(registers);
        let opaque = self.callers_closure(opaque.iter().cloned());
        let fns = |items: &mut dyn Iterator<Item = &MonoItem>| -> HashSet<Instance> {
            items
                .filter_map(|item| match item {
                    MonoItem::Fn(instance) => Some(*instance),
                    _ => None, // external enum: MonoItem
                })
                .collect()
        };
        let address_taken = fns(&mut self
            .edges
            .values()
            .flatten()
            .filter(|succ| succ.0.reason != CollectionReason::DirectCall)
            .map(|succ| &succ.0.item));
        debug!(
            reaching = reaching.len(),
            opaque = opaque.len(),
            address_taken = address_taken.len(),
            "loop-contract reach"
        );
        let visited = fns(&mut collected.iter());
        let clear = visited
            .into_iter()
            .filter(|instance| {
                let item = MonoItem::Fn(*instance);
                !reaching.contains(&item) && !opaque.contains(&item)
            })
            .collect();
        LoopContractReach::new(fns(&mut reaching.iter()), clear, address_taken)
    }

    /// `seeds` and every item with a path to one of them.
    fn callers_closure(&self, seeds: impl Iterator<Item = MonoItem>) -> HashSet<MonoItem> {
        let mut queue: Vec<MonoItem> = seeds.collect();
        let mut closure: HashSet<MonoItem> = HashSet::new();
        while let Some(item) = queue.pop() {
            if closure.contains(&item) {
                continue;
            }
            if let Some(callers) = self.back_edges.get(&Node(item.clone())) {
                queue.extend(callers.iter().map(|caller| caller.0.item.clone()));
            }
            closure.insert(item);
        }
        closure
    }

    /// Add a new node into a graph. Skips edge-map init for existing nodes.
    fn add_node(&mut self, item: &MonoItem) -> Node {
        let node = Node(item.clone());
        if self.nodes.insert(node.clone()) {
            self.edges.entry(node.clone()).or_default();
            self.back_edges.entry(node.clone()).or_default();
        }
        node
    }

    /// Add multiple new edges for the "from" node.
    fn add_edges(&mut self, from: &MonoItem, to: &[CollectedItem]) {
        let from_key = self.add_node(from);
        for CollectedItem { item, reason } in to {
            let to_key = self.add_node(item);
            self.edges
                .get_mut(&from_key)
                .expect("from in edges")
                .push(CollectedNode(CollectedItem { item: item.clone(), reason: *reason }));
            self.back_edges
                .get_mut(&to_key)
                .expect("to in back_edges")
                .push(CollectedNode(CollectedItem { item: from.clone(), reason: *reason }));
        }
    }
}

#[cfg(debug_assertions)]
impl CallGraph {
    /// Print the graph in DOT format to a file.
    /// See <https://graphviz.org/doc/info/lang.html> for more information.
    fn dump_dot(&self, tcx: TyCtxt, initial: Option<MonoItem>) -> std::io::Result<()> {
        if let Ok(target) = std::env::var("TRUST_MC_REACH_DEBUG") {
            debug!(?target, "dump_dot");
            let name = initial.map(|item| Node(item).to_string()).unwrap_or_default();
            let outputs = tcx.output_filenames(());
            let base_path = outputs.path(OutputType::Metadata);
            let file_stem = format!(
                "{}_{}.dot",
                base_path.as_path().file_stem().expect("file stem").to_string_lossy(),
                name
            );
            let path = base_path.as_path().parent().expect("parent path").join(file_stem);
            let out_file = File::create(path)?;
            let mut writer = BufWriter::new(out_file);
            writeln!(writer, "digraph ReachabilityGraph {{")?;
            if target.is_empty() {
                self.dump_all(&mut writer)?;
            } else {
                // Only dump nodes that led the reachability analysis to the target node.
                self.dump_reason(&mut writer, &target)?;
            }
            writeln!(writer, "}}")?;
        }

        Ok(())
    }

    /// Write all notes to the given writer.
    fn dump_all<W: Write>(&self, writer: &mut W) -> std::io::Result<()> {
        tracing::info!(nodes=?self.nodes.len(), edges=?self.edges.len(), "dump_all");
        for node in &self.nodes {
            writeln!(writer, r#""{node}""#)?;
            for succ in self.edges.get(node).expect("node in edges") {
                let reason = succ.0.reason;
                writeln!(writer, r#""{node}" -> "{succ}" [label={reason:?}] "#)?;
            }
        }
        Ok(())
    }

    /// Write all notes that may have led to the discovery of the given target.
    fn dump_reason<W: Write>(&self, writer: &mut W, target: &str) -> std::io::Result<()> {
        let mut queue: Vec<Node> =
            self.nodes.iter().filter(|item| item.to_string().contains(target)).cloned().collect();
        let mut visited: HashSet<Node> = HashSet::default();
        tracing::info!(target=?queue, nodes=?self.nodes.len(), edges=?self.edges.len(), "dump_reason");
        while let Some(to_visit) = queue.pop() {
            if !visited.contains(&to_visit) {
                queue.extend(
                    self.back_edges
                        .get(&to_visit)
                        .expect("node in back_edges")
                        .iter()
                        .map(|item| Node(item.0.item.clone())),
                );
                visited.insert(to_visit);
            }
        }

        for node in &visited {
            writeln!(writer, r#""{node}""#)?;
            let edges = self.edges.get(node).expect("visited node in edges");
            for succ in edges.iter().filter(|item| {
                let node = Node(item.0.item.clone());
                visited.contains(&node)
            }) {
                let reason = succ.0.reason;
                writeln!(writer, r#""{node}" -> "{succ}" [label={reason:?}] "#)?;
            }
        }
        Ok(())
    }
}

impl Display for Node {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            MonoItem::Fn(instance) => write!(f, "{}", instance.name()),
            MonoItem::Static(def) => write!(f, "{}", def.name()),
            MonoItem::GlobalAsm(asm) => write!(f, "{asm:?}"),
        }
    }
}

impl Display for CollectedNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.0.item {
            MonoItem::Fn(instance) => write!(f, "{}", instance.name()),
            MonoItem::Static(def) => write!(f, "{}", def.name()),
            MonoItem::GlobalAsm(asm) => write!(f, "{asm:?}"),
        }
    }
}

impl From<CollectedNode> for Node {
    fn from(value: CollectedNode) -> Self {
        Node(value.0.item)
    }
}
