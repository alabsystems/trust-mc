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
use crate::kani_middle::transform::BodyTransformation;

pub(crate) trait AbstractionBoundary {
    fn has_explicit_stub(&self, path: &str) -> bool;
    /// Returns `true` if the path is backed by a CHC handler (e.g., stable atomic
    /// operations) even without an explicit stub in `StubRegistry`. (Part of #3777)
    fn has_handler_backed_abstraction(&self, path: &str) -> bool;
    fn record_unstubbed_abstraction(&self, path: &str);
}

/// Collect all reachable items starting from the given starting points.
pub(crate) fn collect_reachable_items(
    tcx: TyCtxt,
    transformer: &mut BodyTransformation,
    starting_points: &[MonoItem],
    abstraction_boundary: &dyn AbstractionBoundary,
) -> (Vec<MonoItem>, CallGraph) {
    // For each harness, collect items using the same collector.
    // I.e.: This will return any item that is reachable from one or more of the starting points.
    let mut collector = MonoItemsCollector::new(tcx, transformer, abstraction_boundary);
    for item in starting_points {
        collector.collect(item);
    }

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
    /// Items enqueued for visiting.
    queue: Vec<MonoItem>,
    /// Call graph used for dataflow analysis.
    call_graph: CallGraph,
    /// Backend-specific abstraction/stub policy.
    abstraction_boundary: &'a dyn AbstractionBoundary,
}

impl<'tcx, 'a> MonoItemsCollector<'tcx, 'a> {
    fn new(
        tcx: TyCtxt<'tcx>,
        transformer: &'a mut BodyTransformation,
        abstraction_boundary: &'a dyn AbstractionBoundary,
    ) -> Self {
        MonoItemsCollector {
            tcx,
            collected: FxHashSet::default(),
            abstracted: FxHashSet::default(),
            queue: vec![],
            call_graph: CallGraph::default(),
            transformer,
            abstraction_boundary,
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
                MonoItem::Fn(instance)
                    if is_abstract_function(self.tcx, *instance, self.abstraction_boundary)
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
        if is_abstract_function(self.tcx, instance, self.abstraction_boundary) {
            trace!(?instance, "visit_fn: abstract stub boundary");
            return vec![];
        }
        let body = self.transformer.body_ref(self.tcx, instance);
        let mut collector = MonoItemsFnCollector {
            tcx: self.tcx,
            collected: FxHashSet::default(),
            abstraction_boundary: self.abstraction_boundary,
            body,
        };
        collector.visit_body(body);
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
                        collect_alloc_items(self.tcx, prov.0, self.abstraction_boundary)
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
    abstraction_boundary: &'collector dyn AbstractionBoundary,
    body: &'body Body,
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
                        (should_codegen_locally(&instance)
                            && !is_abstract_function(self.tcx, instance, self.abstraction_boundary))
                        .then_some(MonoItem::Fn(instance))
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
        if is_abstract_function(self.tcx, instance, self.abstraction_boundary) {
            trace!(?instance, "collect_instance: abstract stub boundary");
            return;
        }
        let should_collect = match instance.kind {
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
                collect_alloc_items(self.tcx, id.0, self.abstraction_boundary)
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
                    self.collect_vtable_methods(src_ty, dst_ty);
                }
            }
            Rvalue::Cast(
                CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer),
                ref operand,
                _,
            ) => {
                let fn_kind = operand.ty(self.body.locals()).expect("reify operand type").kind();
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
                _,
            ) => {
                let source_ty = operand.ty(self.body.locals()).expect("closure operand type");
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
                    self.collect_instance(instance, true);
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
        rustc_internal::internal(tcx, item).hash_stable(&mut hcx, &mut hasher);
        hasher.finish()
    })
}

/// Functions that should be abstracted rather than analyzed.
/// Bodies are NOT collected; codegen emits SMT stubs instead.
///
/// Per designs/archive/2026-02-01-reachability-intercept-fix.md:
/// The root cause of collection test failures is that stubs intercept at codegen time,
/// but the reachability collector has already fetched all internal function bodies.
/// We intercept at reachability level using prefix matching to prevent internal
/// bodies (node::NodeRef, search::search_tree, etc.) from being collected.
const ABSTRACT_FUNCTION_PREFIXES: &[&str] = &[
    // Collections - modeled as SMT arrays (Part of #1659)
    "std::collections::BTreeSet::",
    "std::collections::BTreeMap::",
    "std::collections::HashMap::",
    "std::collections::HashSet::",
    // Module-level paths for HashMap/HashSet iterator types (Part of #3057).
    // Iterator types live in std::collections::hash_map/hash_set modules, not on
    // the type path. Without these, IntoIter::next/Iter::next get inlined,
    // exposing hashbrown internals (Bucket::read, ControlFlow) that CHC can't handle.
    "std::collections::hash_map::",
    "std::collections::hash_set::",
    // hashbrown internals — HashMap/HashSet delegate to hashbrown internally.
    // Inlining hashbrown functions exposes raw pointer ops and internal types
    // (RawTable, Bucket, RawIter) that have no CHC stubs.
    "hashbrown::",
    "std::collections::btree_map::",
    "std::collections::btree_set::",
    "alloc::collections::btree_set::BTreeSet::",
    "alloc::collections::btree_map::BTreeMap::",
    "alloc::collections::btree::", // Internal BTree modules (node, search, etc.)
    // Vec/String - modeled as SMT sequences or arrays
    "alloc::vec::Vec::",
    "alloc::vec::into_iter::", // IntoIter internals — without this, rustc inlines next() into raw ptr ops (#2876 RC2)
    "std::vec::Vec::", // std re-export of alloc::vec::Vec — def_path_str() returns this form (#2967)
    "std::vec::IntoIter::", // std re-export of alloc::vec::into_iter::IntoIter (#2967)
    "alloc::string::String::",
    "std::string::String::", // std re-export of alloc::string::String (#2967)
    // Cow<str> - collapse to String (#1691)
    // from_utf8_lossy returns Cow<str> but we model as String
    "std::borrow::Cow::",
    "alloc::borrow::Cow::",
    // UTF-8 lossy conversion internals - Utf8Chunks iterator
    // from_utf8_lossy internally uses Utf8Chunks which we don't need to model
    "core::str::lossy::", // Utf8Chunks, Utf8Chunk implementation
    "core::str::Utf8Chunk::",
    "core::str::Utf8Chunks::",
    "alloc::str::Utf8Chunk::",
    "alloc::str::Utf8Chunks::",
    "std::str::Utf8Chunk::",
    "std::str::Utf8Chunks::",
    // Allocation internals - already stubbed, prevent body collection (#1691)
    // RawVec is Vec's internal buffer manager - MIR bodies cause codegen explosion
    "alloc::raw_vec::", // RawVec, RawVecInner
    // Global allocator inherent methods (not trait impls - those use <Global as Allocator>::...)
    // This matches paths like std::alloc::Global::alloc_impl
    "std::alloc::Global::",
    // Slice conversion internals — vec![...] macro expansion path (#2967)
    // <[T]>::into_vec / alloc::slice::hack::into_vec converts Box<[T]> to Vec<T>.
    // Without this, into_vec body gets inlined, introducing concrete MIR with obj_valid
    // checks that create dual-model mismatch with abstract Vec stubs.
    "alloc::slice::",
    // Slice module — covers both method impls (<[T]>::iter, iter_mut) and iterator internals
    // (core::slice::iter::Iter::next, IterMut::next). The broad core::slice:: prefix
    // subsumes the more specific core::slice::iter:: (#3012). Blocking body collection
    // forces Call preservation for VecIter/VecIterMut stub dispatch. Also covers stubs:
    // SlicePartialEqEqual, SliceIndexIndex, PtrCast.
    "core::slice::",
    // std re-export of core::slice — Instance::name() may return std::slice:: for some
    // resolved instances (#3012). Subsumes std::slice::iter::.
    "std::slice::",
    // VecDeque — ring buffer backed by RawVec. MIR bodies involve raw pointer arithmetic
    // for head/tail wrapping that the solver cannot reason about. Test harness:
    // tests/expected/vecdq/main.rs uses stdlib VecDeque directly. (Part of #2984)
    "std::collections::VecDeque::",
    "std::collections::vec_deque::", // Internal VecDeque module (iter, drain, etc.)
    "alloc::collections::vec_deque::", // alloc-level VecDeque path
    // LinkedList — doubly-linked with raw NonNull pointers. Test harness:
    // tests/expected/object-bits/insufficient/main.rs uses stdlib LinkedList.
    // MIR bodies are pointer-heavy and cause state explosion. (Part of #2984)
    "std::collections::LinkedList::",
    "std::collections::linked_list::", // Internal LinkedList module
    "alloc::collections::linked_list::", // alloc-level LinkedList path
    // Range iterator internals — spec_next is the CHC-stubbed entry point (#3002)
    // Without this, the inline pass inlines spec_next's body. At Reg level the inlined
    // MIR happens to work, but at Mem level the field accesses through &mut self require
    // memory model resolution that fails for flattened Range locals. By preventing
    // inlining, the Call terminator for spec_next is preserved for CHC dispatch as
    // RangeSpecNext, which produces correct flattened-field constraints.
    // Path: <std::ops::Range<T> as std::iter::range::RangeIteratorImpl>::spec_next
    "core::iter::range::RangeIteratorImpl::",
    "std::iter::range::RangeIteratorImpl::",
    // Atomic types — stable API wrappers add MIR complexity that defeats PDR.
    // Raw intrinsic calls (atomic_load, atomic_xadd, etc.) are already handled
    // by try_dispatch_call_atomic. Stable wrappers (AtomicBool::load, etc.)
    // produce Ordering enum match + compiler_fence + field access wrapper MIR
    // that inflates CHC clause count 3-5x vs bare intrinsic encoding.
    // Abstraction boundary prevents this inflation — the Call terminator is
    // preserved for CHC dispatch as a stable atomic stub. (Part of #3452)
    "core::sync::atomic::",
    "std::sync::atomic::",
    // Mutex/RwLock — transparent wrappers in single-threaded verification (Part of #4067).
    // MIR bodies contain pthread foreign calls that create unconstrained memory.
    // inline_known_calls handles new/into_inner/get_mut as identity;
    // generic_preroutes handles lock/read/write as always-Ok.
    // Drop is a no-op (transparent wrapper drop = drop inner T only).
    "std::sync::Mutex::",
    "std::sync::RwLock::",
    "std::sync::MutexGuard::",
    "std::sync::RwLockReadGuard::",
    "std::sync::RwLockWriteGuard::",
    // Filesystem operations — pure OS side effects with no verification semantics.
    // Without this, remove_file inlines run_with_cstr → unlink, producing
    // recursion unwinding assertions from platform abstraction layer internals.
    // Part of #4134.
    "std::fs::",
];

/// Method name fragments exempted from prefix abstraction.
///
/// These methods have complex control flow (loops, closures) that requires MIR body
/// collection for correct CHC encoding. Inner calls to other abstracted methods
/// (e.g., `load`, `compare_exchange_weak`) are still caught by their respective
/// CHC stubs when the exempted method's body is inlined.
///
/// Matched via `path.contains(fragment)` so generic monomorphizations like
/// `AtomicPtr::<i32>::fetch_update::<{closure@...}>` still match.
///
/// Part of #3516: `fetch_update` contains a CAS loop with a closure call.
/// In the sequential model the loop always succeeds on the first iteration,
/// but the closure must be dispatched normally — no CHC stub can evaluate it.
const ABSTRACT_PREFIX_EXCEPTIONS: &[&str] = &["::fetch_update"];

/// Check whether a function path matches the prefix-based abstraction list.
///
/// This is the core reachability-boundary logic: functions matching these prefixes
/// have their bodies skipped during collection (codegen emits SMT stubs instead).
///
/// For trait impl paths like `<alloc::raw_vec::RawVec<T, A> as std::ops::Drop>::drop`,
/// we use `contains()` since they don't start with the module path.
/// For Cow<str> matching, we strip trailing `::` from prefixes since generic params
/// come before `::` (e.g., `std::borrow::Cow::` should match `std::borrow::Cow<str>`).
pub(crate) fn is_prefix_abstracted(path: &str) -> bool {
    // Exception: specific methods need body collection for MIR inlining even
    // though their containing module is abstracted. Monomorphized paths include
    // type parameters after the method name (e.g., `::fetch_update::<{closure@...}>`),
    // so we use `contains()` instead of exact-match on the last segment. (Part of #3516)
    if ABSTRACT_PREFIX_EXCEPTIONS.iter().any(|frag| path.contains(frag)) {
        return false;
    }
    // Normalize duplicated `std::` prefix from MIR re-exports (Part of #4231).
    // `def_path_str()` can produce `std::std::fs::remove_file` when std re-exports
    // items from itself. Collapse repeated leading `std::` before matching.
    let normalized = normalize_std_prefix(path);
    ABSTRACT_FUNCTION_PREFIXES.iter().any(|prefix| {
        if normalized.starts_with(prefix) {
            return true;
        }
        if normalized.starts_with('<') {
            let prefix_base = prefix.strip_suffix("::").unwrap_or(prefix);
            return normalized.contains(prefix_base);
        }
        false
    })
}

/// Normalize paths with duplicated `std::` prefix from MIR re-exports.
///
/// After MIR inlining or std re-exports, `def_path_str()` can produce paths like
/// `std::std::fs::remove_file` where the `std::` prefix is doubled.
/// This collapses repeated leading `std::` segments into a single one.
fn normalize_std_prefix(path: &str) -> &str {
    let mut s = path;
    while s.starts_with("std::std::") {
        s = &s[5..]; // strip one "std::" (5 bytes)
    }
    s
}

/// Known stdlib type keywords that the prefix list MUST cover. Used for runtime
/// drift detection (Part of #2984): if `def_path_str()` returns a path containing
/// one of these keywords in a stdlib context, `is_prefix_abstracted()` SHOULD match it.
/// When a mismatch is detected, a diagnostic warning is emitted so toolchain-induced
/// path format changes are caught rather than causing silent state explosion.
///
/// Each entry is (path_fragment, label). A path matches if it contains the fragment.
///
/// NOTE: BinaryHeap is intentionally excluded — it is tree-based like BTreeMap
/// and would need stubs, but no test harness currently uses it. Adding it here
/// without stubs would cause unconstrained-result warnings without benefit.
const KNOWN_ABSTRACTED_TYPE_KEYWORDS: &[(&str, &str)] = &[
    ("alloc::vec::Vec", "Vec"),
    ("alloc::string::String", "String"),
    ("alloc::borrow::Cow", "Cow"),
    ("alloc::raw_vec::RawVec", "RawVec"),
    ("alloc::collections::btree_map::BTreeMap", "BTreeMap"),
    ("alloc::collections::btree_set::BTreeSet", "BTreeSet"),
    ("std::collections::HashMap", "HashMap"),
    ("std::collections::HashSet", "HashSet"),
    ("std::collections::VecDeque", "VecDeque"),
    ("std::collections::LinkedList", "LinkedList"),
    ("alloc::slice::", "slice"),
    ("core::slice::", "slice"),
    ("core::str::lossy::", "Utf8Chunks"),
    ("core::sync::atomic::", "Atomic"),
];

/// Track functions that have already been warned about to avoid duplicate warnings.
/// Per designs/archive/2026-02-01-stub-coverage-validation.md: warning deduplication
static WARNED_UNSTUBBED_FUNCTIONS: OnceLock<Mutex<HashSet<String>>> = OnceLock::new();

/// Track drift-detection warnings to avoid duplicates (Part of #2984).
static WARNED_DRIFT_FUNCTIONS: OnceLock<Mutex<HashSet<String>>> = OnceLock::new();

fn is_abstract_function(
    tcx: TyCtxt,
    instance: Instance,
    abstraction_boundary: &dyn AbstractionBoundary,
) -> bool {
    let def_id = instance.def.def_id();
    let internal_def_id = rustc_internal::internal(tcx, def_id);
    let path = tcx.def_path_str(internal_def_id);

    let has_stub = abstraction_boundary.has_explicit_stub(&path);

    let is_prefix_match = is_prefix_abstracted(&path);

    if is_prefix_match {
        trace!(?path, "is_abstract_function: prefix match -> abstracted");

        // Handler-backed abstractions (e.g., stable atomic ops) have CHC handlers
        // even without explicit stubs — no warning needed. (Part of #3777)
        let has_handler = abstraction_boundary.has_handler_backed_abstraction(&path);

        // Emit warning if prefix-abstracted without stub AND not handler-backed
        // Per designs/archive/2026-02-01-stub-coverage-validation.md
        if !has_stub && !has_handler {
            // Track unstubbed abstraction for summary (Part of #1685)
            abstraction_boundary.record_unstubbed_abstraction(&path);

            let warned_set = WARNED_UNSTUBBED_FUNCTIONS.get_or_init(|| Mutex::new(HashSet::new()));
            let mut warned = warned_set.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
            // Check contains first to avoid String allocation when already warned
            if !warned.contains(&path) {
                tcx.dcx().warn(format!(
                    "Function `{}` is abstracted but has no stub; result will be unconstrained.",
                    path
                ));
                warned.insert(path); // No clone needed - path not used after
            }
        }
        return true;
    }

    // Drift detection (Part of #2984): if this function's path contains a known
    // type keyword but was NOT caught by is_prefix_abstracted(), the prefix list
    // may have drifted from def_path_str() output. This catches toolchain bumps
    // that silently change canonical paths without updating the prefix list.
    if !has_stub {
        for &(fragment, label) in KNOWN_ABSTRACTED_TYPE_KEYWORDS {
            if path.contains(fragment) {
                let drift_set = WARNED_DRIFT_FUNCTIONS.get_or_init(|| Mutex::new(HashSet::new()));
                let mut warned =
                    drift_set.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
                if !warned.contains(&path) {
                    debug!(
                        ?path,
                        label,
                        "drift detection: stdlib function collected \
                         (not caught by ABSTRACT_FUNCTION_PREFIXES)"
                    );
                    warned.insert(path);
                }
                break;
            }
        }
    }

    // Fall back to exact stub matching for other stubbed functions
    has_stub
}

/// Return whether we should include the item into codegen.
fn should_codegen_locally(instance: &Instance) -> bool {
    !instance.is_foreign_item()
}

fn collect_alloc_items(
    tcx: TyCtxt,
    alloc_id: AllocId,
    abstraction_boundary: &dyn AbstractionBoundary,
) -> Vec<MonoItem> {
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
                    items.extend(alloc.provenance.ptrs.iter().flat_map(|(_, prov)| {
                        collect_alloc_items(tcx, prov.0, abstraction_boundary)
                    }));
                }
            } else {
                // This differ from rustc's collector since rustc does not include static from
                // upstream crates.
                let instance = Instance::try_from(CrateItem::from(def)).expect("static instance");
                should_codegen_locally(&instance).then(|| items.push(MonoItem::from(def)));
            }
        }
        GlobalAlloc::Function(instance) => {
            if should_codegen_locally(&instance)
                && !is_abstract_function(tcx, instance, abstraction_boundary)
            {
                items.push(MonoItem::from(instance));
            }
        }
        GlobalAlloc::Memory(alloc) => {
            items.extend(
                alloc
                    .provenance
                    .ptrs
                    .iter()
                    .flat_map(|(_, prov)| collect_alloc_items(tcx, prov.0, abstraction_boundary)),
            );
        }
        vtable_alloc @ GlobalAlloc::VTable(..) => {
            let vtable_id = vtable_alloc.vtable_allocation().expect("vtable allocation");
            items = collect_alloc_items(tcx, vtable_id, abstraction_boundary);
        }
        GlobalAlloc::TypeId { ty: _ } => {}
    }
    items
}

/// Call graph with edges annotated with the reason why they were added to the graph.
#[derive(Debug, Default)]
pub(crate) struct CallGraph {
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

#[cfg(test)]
mod tests {
    use super::is_prefix_abstracted;

    // --- Direct prefix matches (path starts with a prefix) ---

    #[test]
    fn test_btreeset_direct_method() {
        assert!(is_prefix_abstracted("std::collections::BTreeSet::insert"));
    }

    #[test]
    fn test_btreemap_direct_method() {
        assert!(is_prefix_abstracted("std::collections::BTreeMap::get"));
    }

    #[test]
    fn test_hashmap_direct_method() {
        assert!(is_prefix_abstracted("std::collections::HashMap::insert"));
    }

    #[test]
    fn test_hashset_direct_method() {
        assert!(is_prefix_abstracted("std::collections::HashSet::contains"));
    }

    #[test]
    fn test_alloc_btree_internal() {
        assert!(is_prefix_abstracted("alloc::collections::btree::node::NodeRef::new"));
    }

    #[test]
    fn test_vec_direct_method() {
        assert!(is_prefix_abstracted("alloc::vec::Vec::push"));
    }

    #[test]
    fn test_string_direct_method() {
        assert!(is_prefix_abstracted("alloc::string::String::from"));
    }

    #[test]
    fn test_cow_std_method() {
        assert!(is_prefix_abstracted("std::borrow::Cow::into_owned"));
    }

    #[test]
    fn test_raw_vec_internal() {
        assert!(is_prefix_abstracted("alloc::raw_vec::RawVec::grow_amortized"));
    }

    #[test]
    fn test_global_alloc_impl() {
        assert!(is_prefix_abstracted("std::alloc::Global::alloc_impl"));
    }

    #[test]
    fn test_utf8_chunks_internal() {
        assert!(is_prefix_abstracted("core::str::lossy::Utf8Chunks::next"));
    }

    // --- Trait impl paths (angle-bracket paths use contains-based matching) ---

    #[test]
    fn test_rawvec_drop_trait_impl() {
        assert!(is_prefix_abstracted("<alloc::raw_vec::RawVec<T, A> as std::ops::Drop>::drop"));
    }

    #[test]
    fn test_cow_tostring_trait_impl() {
        assert!(is_prefix_abstracted("<std::borrow::Cow<str> as ToString>::to_string"));
    }

    #[test]
    fn test_btreemap_trait_impl() {
        assert!(is_prefix_abstracted(
            "<alloc::collections::btree_map::BTreeMap<K, V> as Clone>::clone"
        ));
    }

    #[test]
    fn test_hashmap_trait_impl() {
        assert!(is_prefix_abstracted("<std::collections::HashMap<K, V> as Default>::default"));
    }

    #[test]
    fn test_vec_trait_impl() {
        assert!(is_prefix_abstracted("<alloc::vec::Vec<T> as Extend<T>>::extend"));
    }

    // --- Non-matching paths (should NOT be abstracted) ---

    #[test]
    fn test_user_function_not_abstracted() {
        assert!(!is_prefix_abstracted("my_crate::my_module::my_function"));
    }

    #[test]
    fn test_core_ops_not_abstracted() {
        assert!(!is_prefix_abstracted("core::ops::Add::add"));
    }

    #[test]
    fn test_std_io_not_abstracted() {
        assert!(!is_prefix_abstracted("std::io::Write::write"));
    }

    #[test]
    fn test_non_trait_angle_bracket_no_match() {
        // Angle-bracket path that doesn't contain any abstracted prefix base
        assert!(!is_prefix_abstracted("<i32 as core::fmt::Display>::fmt"));
    }

    #[test]
    fn test_partial_prefix_no_false_positive() {
        // "std::collections::BTree" without "Set::" or "Map::" suffix should not match
        assert!(!is_prefix_abstracted("std::collections::BTree"));
    }

    #[test]
    fn test_empty_path() {
        assert!(!is_prefix_abstracted(""));
    }

    // --- Edge cases for the Cow/trait-impl stripping logic ---

    #[test]
    fn test_alloc_cow_trait_impl() {
        assert!(is_prefix_abstracted("<alloc::borrow::Cow<str> as Display>::fmt"));
    }

    #[test]
    fn test_btreeset_alloc_path() {
        assert!(is_prefix_abstracted("alloc::collections::btree_set::BTreeSet::insert"));
    }

    #[test]
    fn test_btree_search_internal() {
        assert!(is_prefix_abstracted("alloc::collections::btree::search::search_tree"));
    }

    // --- Prefixes missing from initial coverage (self-audit W3-785a) ---

    #[test]
    fn test_std_btree_map_module() {
        assert!(is_prefix_abstracted("std::collections::btree_map::OccupiedEntry::get"));
    }

    #[test]
    fn test_std_btree_set_module() {
        assert!(is_prefix_abstracted("std::collections::btree_set::Intersection::next"));
    }

    #[test]
    fn test_core_str_utf8chunk() {
        assert!(is_prefix_abstracted("core::str::Utf8Chunk::valid"));
    }

    #[test]
    fn test_core_str_utf8chunks() {
        assert!(is_prefix_abstracted("core::str::Utf8Chunks::next"));
    }

    #[test]
    fn test_alloc_str_utf8chunk() {
        assert!(is_prefix_abstracted("alloc::str::Utf8Chunk::valid"));
    }

    #[test]
    fn test_alloc_str_utf8chunks() {
        assert!(is_prefix_abstracted("alloc::str::Utf8Chunks::next"));
    }

    #[test]
    fn test_std_str_utf8chunk() {
        assert!(is_prefix_abstracted("std::str::Utf8Chunk::valid"));
    }

    #[test]
    fn test_std_str_utf8chunks() {
        assert!(is_prefix_abstracted("std::str::Utf8Chunks::next"));
    }

    // --- Vec IntoIter paths (#2876 RC2) ---

    #[test]
    fn test_vec_into_iter_next() {
        assert!(is_prefix_abstracted("alloc::vec::into_iter::IntoIter::<i32>::next"));
    }

    #[test]
    fn test_vec_into_iter_trait_impl() {
        assert!(is_prefix_abstracted("<alloc::vec::into_iter::IntoIter<i32> as Iterator>::next"));
    }

    // --- std:: re-export paths (#2967: dual-model mismatch fix) ---
    // def_path_str() returns std:: re-export paths for public types.
    // Without these, concrete MIR bodies leak through the abstraction boundary,
    // creating dual-model (abstract stub + concrete MIR) that causes spurious CTREX.

    #[test]
    fn test_std_vec_direct_method() {
        assert!(is_prefix_abstracted("std::vec::Vec::<i32>::push"));
    }

    #[test]
    fn test_std_vec_new() {
        assert!(is_prefix_abstracted("std::vec::Vec::<i32>::new"));
    }

    #[test]
    fn test_std_vec_into_iter_direct_method() {
        assert!(is_prefix_abstracted("std::vec::IntoIter::<i32>::as_raw_mut_slice"));
    }

    #[test]
    fn test_std_vec_into_iter_drop_trait_impl() {
        // This is the critical path: Drop::drop for IntoIter was the primary
        // leakage vector allowing concrete MIR (NonNull, RawVec, ManuallyDrop)
        // into the CHC encoding alongside abstract stubs.
        assert!(is_prefix_abstracted("<std::vec::IntoIter<T, A> as std::ops::Drop>::drop"));
    }

    #[test]
    fn test_std_vec_into_iter_iterator_trait_impl() {
        assert!(is_prefix_abstracted(
            "<std::vec::IntoIter<i32> as core::iter::traits::iterator::Iterator>::next"
        ));
    }

    #[test]
    fn test_std_vec_into_iterator_trait_impl() {
        assert!(is_prefix_abstracted(
            "<std::vec::Vec<i32> as core::iter::traits::collect::IntoIterator>::into_iter"
        ));
    }

    #[test]
    fn test_std_string_direct_method() {
        assert!(is_prefix_abstracted("std::string::String::from"));
    }

    #[test]
    fn test_std_string_trait_impl() {
        assert!(is_prefix_abstracted("<std::string::String as core::fmt::Display>::fmt"));
    }

    // --- drop_in_place shims: intentionally NOT abstracted (#2967 design) ---
    // drop_in_place shims are compiler-generated wrappers that call <T as Drop>::drop.
    // They are NOT in ABSTRACT_FUNCTION_PREFIXES because:
    // 1. Their bodies are trivial (call Drop::drop + field drops)
    // 2. The Drop::drop callee IS caught by the prefix match (contains-based)
    // 3. Field drops for non-Box types are no-op goto rules in CHC
    // 4. Abstracting all drop_in_place globally would break Drop semantics

    #[test]
    fn test_drop_in_place_not_abstracted() {
        assert!(!is_prefix_abstracted("std::ptr::drop_in_place::<std::vec::IntoIter<i32>>"));
    }

    #[test]
    fn test_core_drop_in_place_not_abstracted() {
        assert!(!is_prefix_abstracted("core::ptr::drop_in_place::<alloc::vec::Vec<i32>>"));
    }

    // --- Pointer internals: NOT directly abstracted (#2967) ---
    // NonNull, ManuallyDrop, RawVecInner are only excluded transitively
    // (their callers — Vec, IntoIter, RawVec — are abstracted, so they're
    // never reached). They are NOT in the prefix list.

    #[test]
    fn test_nonnull_not_abstracted() {
        assert!(!is_prefix_abstracted("core::ptr::non_null::NonNull::<i32>::as_ptr"));
    }

    #[test]
    fn test_manually_drop_not_abstracted() {
        assert!(!is_prefix_abstracted("core::mem::ManuallyDrop::<i32>::drop"));
    }

    // --- Allocator trait impl: caught via contains-based matching ---
    // <std::alloc::Global as Allocator>::allocate matches because
    // "std::alloc::Global" (prefix base) is contained in the path.

    #[test]
    fn test_global_allocator_trait_impl() {
        assert!(is_prefix_abstracted("<std::alloc::Global as core::alloc::Allocator>::allocate"));
    }

    // Note: alloc::alloc::Global (internal path) is NOT covered by the prefix
    // list. This is safe because Global is only reached via RawVec (which IS
    // excluded via alloc::raw_vec:: prefix). If def_path_str ever returns the
    // internal alloc::alloc::Global path for a reachable function, this would
    // be a gap. The test below documents this known theoretical gap.
    #[test]
    fn test_alloc_internal_global_not_covered() {
        // This is a known gap — safe because Global is only reached from excluded RawVec.
        assert!(!is_prefix_abstracted("alloc::alloc::Global::alloc_impl"));
    }

    // --- Range iterator: RangeIteratorImpl abstracted (#3002) ---
    // spec_next is the CHC-stubbed entry point for Range for-loop encoding.
    // Without abstraction, the inline pass inlines it, breaking Mem-level encoding.

    #[test]
    fn test_range_iterator_impl_spec_next_abstracted() {
        assert!(is_prefix_abstracted(
            "<std::ops::Range<u32> as std::iter::range::RangeIteratorImpl>::spec_next"
        ));
    }

    #[test]
    fn test_range_iterator_impl_core_path_abstracted() {
        assert!(is_prefix_abstracted(
            "<core::ops::range::Range<u32> as core::iter::range::RangeIteratorImpl>::spec_next"
        ));
    }

    #[test]
    fn test_range_next_not_abstracted() {
        // Range::next() itself should NOT be abstracted — only spec_next.
        // next() must be inlined so its Call to spec_next is exposed.
        assert!(!is_prefix_abstracted(
            "<std::ops::Range<u32> as std::iter::traits::iterator::Iterator>::next"
        ));
    }

    // --- VecDeque paths (Part of #2984) ---

    #[test]
    fn test_vecdeque_direct_method() {
        assert!(is_prefix_abstracted("std::collections::VecDeque::<i32>::push_back"));
    }

    #[test]
    fn test_vecdeque_module_internal() {
        assert!(is_prefix_abstracted("std::collections::vec_deque::Iter::<i32>::next"));
    }

    #[test]
    fn test_vecdeque_alloc_path() {
        assert!(is_prefix_abstracted("alloc::collections::vec_deque::VecDeque::<i32>::pop_front"));
    }

    #[test]
    fn test_vecdeque_trait_impl() {
        assert!(is_prefix_abstracted(
            "<std::collections::VecDeque<i32> as core::iter::traits::collect::IntoIterator>::into_iter"
        ));
    }

    // --- LinkedList paths (Part of #2984) ---

    #[test]
    fn test_linked_list_direct_method() {
        assert!(is_prefix_abstracted("std::collections::LinkedList::<i32>::push_back"));
    }

    #[test]
    fn test_linked_list_module_internal() {
        assert!(is_prefix_abstracted("std::collections::linked_list::Iter::<i32>::next"));
    }

    #[test]
    fn test_linked_list_alloc_path() {
        assert!(is_prefix_abstracted(
            "alloc::collections::linked_list::LinkedList::<i32>::push_front"
        ));
    }

    #[test]
    fn test_linked_list_trait_impl() {
        assert!(is_prefix_abstracted(
            "<std::collections::LinkedList<i32> as core::iter::traits::collect::IntoIterator>::into_iter"
        ));
    }

    // --- Structural validation of ABSTRACT_FUNCTION_PREFIXES (Part of #2984) ---
    // These tests validate invariants of the prefix list itself, catching malformed
    // entries, duplicates, and redundant entries at compile time rather than waiting
    // for a runtime failure.

    #[test]
    fn test_all_prefixes_end_with_separator() {
        for prefix in super::ABSTRACT_FUNCTION_PREFIXES {
            assert!(
                prefix.ends_with("::"),
                "Prefix must end with '::' for correct starts_with matching: {prefix:?}"
            );
        }
    }

    #[test]
    fn test_all_prefixes_start_with_known_root() {
        let valid_roots = ["std::", "alloc::", "core::", "hashbrown::"];
        for prefix in super::ABSTRACT_FUNCTION_PREFIXES {
            assert!(
                valid_roots.iter().any(|root| prefix.starts_with(root)),
                "Prefix must start with std::, alloc::, or core:: (got {prefix:?})"
            );
        }
    }

    #[test]
    fn test_no_duplicate_prefixes() {
        let mut seen = std::collections::HashSet::new();
        for prefix in super::ABSTRACT_FUNCTION_PREFIXES {
            assert!(
                seen.insert(prefix),
                "Duplicate prefix in ABSTRACT_FUNCTION_PREFIXES: {prefix:?}"
            );
        }
    }

    #[test]
    fn test_no_redundant_prefixes() {
        // A prefix is redundant if another shorter prefix already covers it.
        // e.g., "alloc::collections::btree::" covers "alloc::collections::btree_set::"
        // is NOT redundant (different substring), but "alloc::vec::Vec::push::" would be
        // redundant given "alloc::vec::Vec::".
        for (i, prefix) in super::ABSTRACT_FUNCTION_PREFIXES.iter().enumerate() {
            for (j, other) in super::ABSTRACT_FUNCTION_PREFIXES.iter().enumerate() {
                assert!(
                    !(i != j && prefix.starts_with(other)),
                    "Redundant prefix: {prefix:?} is already covered by {other:?}"
                );
            }
        }
    }

    #[test]
    fn test_known_types_have_prefix_coverage() {
        // Cross-reference: every known abstracted type keyword must match at least
        // one prefix via is_prefix_abstracted(). This ensures KNOWN_ABSTRACTED_TYPE_KEYWORDS
        // and ABSTRACT_FUNCTION_PREFIXES stay in sync.
        let test_paths: &[(&str, &str)] = &[
            ("alloc::vec::Vec::<i32>::push", "Vec"),
            ("alloc::string::String::from", "String"),
            ("std::borrow::Cow::<str>::into_owned", "Cow"),
            ("alloc::raw_vec::RawVec::<i32>::grow_amortized", "RawVec"),
            ("std::collections::BTreeMap::<i32, i32>::insert", "BTreeMap"),
            ("std::collections::BTreeSet::<i32>::insert", "BTreeSet"),
            ("std::collections::HashMap::<i32, i32>::insert", "HashMap"),
            ("std::collections::HashSet::<i32>::insert", "HashSet"),
            ("std::collections::VecDeque::<i32>::push_back", "VecDeque"),
            ("std::collections::LinkedList::<i32>::push_back", "LinkedList"),
            ("alloc::slice::hack::into_vec", "slice"),
            ("core::slice::iter::Iter::<i32>::next", "slice iter"),
            ("core::str::lossy::Utf8Chunks::next", "Utf8Chunks"),
            ("core::iter::range::RangeIteratorImpl::spec_next", "RangeIteratorImpl"),
            ("core::sync::atomic::AtomicBool::load", "Atomic"),
        ];
        for &(path, label) in test_paths {
            assert!(
                is_prefix_abstracted(path),
                "Known abstracted type {label:?} not caught for path: {path:?}"
            );
        }
    }

    #[test]
    fn test_drift_keywords_are_reachable() {
        // Validate that every entry in KNOWN_ABSTRACTED_TYPE_KEYWORDS would
        // actually match a path that is_prefix_abstracted() covers. This ensures
        // the drift detection list doesn't contain stale keywords.
        for &(fragment, label) in super::KNOWN_ABSTRACTED_TYPE_KEYWORDS {
            // Construct a synthetic path using the fragment
            let test_path = if fragment.ends_with("::") {
                format!("{fragment}SomeMethod")
            } else {
                format!("{fragment}::some_method")
            };
            assert!(
                is_prefix_abstracted(&test_path),
                "Drift keyword {label:?} (fragment={fragment:?}) not covered \
                 by prefix list (test path: {test_path:?})"
            );
        }
    }

    // --- HashMap/HashSet module-path iterators (Part of #3057) ---
    // Iterator types live in std::collections::hash_map/hash_set modules, not on
    // the HashMap/HashSet type path. Without these, IntoIter::next gets inlined,
    // exposing hashbrown internals.

    #[test]
    fn test_hashmap_into_iter_next_abstracted() {
        assert!(is_prefix_abstracted("std::collections::hash_map::IntoIter::<i32, i32>::next"));
    }

    #[test]
    fn test_hashmap_iter_next_trait_impl_abstracted() {
        assert!(is_prefix_abstracted(
            "<std::collections::hash_map::IntoIter<i32, i32> as core::iter::Iterator>::next"
        ));
    }

    #[test]
    fn test_hashset_into_iter_next_abstracted() {
        assert!(is_prefix_abstracted("std::collections::hash_set::IntoIter::<i32>::next"));
    }

    #[test]
    fn test_hashbrown_raw_table_abstracted() {
        assert!(is_prefix_abstracted("hashbrown::raw::RawTable::<(i32, i32)>::find"));
    }

    #[test]
    fn test_hashbrown_bucket_read_abstracted() {
        assert!(is_prefix_abstracted("hashbrown::raw::Bucket::<(i32, i32)>::read"));
    }

    // --- BinaryHeap: intentionally NOT abstracted (Part of #2984 assessment) ---
    // BinaryHeap is absent because:
    // 1. No test harness currently uses std::collections::BinaryHeap
    // 2. Adding a prefix without corresponding stubs would suppress MIR collection
    //    but produce unconstrained results — worse than state explosion
    // 3. If a future harness needs BinaryHeap, add both stubs and prefix entries
    #[test]
    fn test_binary_heap_intentionally_not_abstracted() {
        assert!(!is_prefix_abstracted("std::collections::BinaryHeap::<i32>::push"));
    }

    // --- Stable atomic API: abstracted to prevent wrapper MIR inflation (Part of #3452) ---

    #[test]
    fn test_atomic_bool_load_abstracted() {
        assert!(is_prefix_abstracted("core::sync::atomic::AtomicBool::load"));
    }

    #[test]
    fn test_atomic_isize_fetch_add_abstracted() {
        assert!(is_prefix_abstracted("std::sync::atomic::AtomicIsize::fetch_add"));
    }

    #[test]
    fn test_atomic_u32_store_abstracted() {
        assert!(is_prefix_abstracted("core::sync::atomic::AtomicU32::store"));
    }

    #[test]
    fn test_atomic_fence_abstracted() {
        assert!(is_prefix_abstracted("std::sync::atomic::fence"));
    }

    #[test]
    fn test_atomic_trait_impl_abstracted() {
        assert!(is_prefix_abstracted("<std::sync::atomic::AtomicBool as core::fmt::Debug>::fmt"));
    }

    // --- Double std:: prefix normalization (#4231) ---
    // MIR inlining / re-exports can produce paths with duplicated `std::` prefix.
    // is_prefix_abstracted must normalize these before matching.

    #[test]
    fn test_double_std_fs_remove_file() {
        assert!(is_prefix_abstracted("std::std::fs::remove_file"));
    }

    #[test]
    fn test_double_std_fs_write() {
        assert!(is_prefix_abstracted("std::std::fs::write"));
    }

    #[test]
    fn test_double_std_collections_vec() {
        assert!(is_prefix_abstracted("std::std::vec::Vec::<i32>::push"));
    }

    #[test]
    fn test_triple_std_prefix() {
        // Even triple-std prefix should be collapsed
        assert!(is_prefix_abstracted("std::std::std::fs::remove_file"));
    }

    #[test]
    fn test_normalize_std_prefix_identity() {
        assert_eq!(super::normalize_std_prefix("std::fs::remove_file"), "std::fs::remove_file");
    }

    #[test]
    fn test_normalize_std_prefix_double() {
        assert_eq!(
            super::normalize_std_prefix("std::std::fs::remove_file"),
            "std::fs::remove_file"
        );
    }

    #[test]
    fn test_normalize_std_prefix_triple() {
        assert_eq!(
            super::normalize_std_prefix("std::std::std::fs::remove_file"),
            "std::fs::remove_file"
        );
    }

    #[test]
    fn test_normalize_std_prefix_non_std() {
        assert_eq!(super::normalize_std_prefix("core::fs::remove_file"), "core::fs::remove_file");
    }
}
