// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The per-harness dyn-coercion universe (design 3, D2, in
//! `docs/chc-hole-fix-designs-2026-09-24.md`).
//!
//! A `dyn Trait` value comes into existence only where a concrete type is
//! unsized to a trait object: an `Unsize` pointer coercion in some body, or a
//! vtable a constant or static holds. The reachability collector visits every
//! body a harness can reach and sees each such coercion, so the set it records
//! is every runtime type a `dyn Trait` receiver in that harness can have.
//!
//! The CHC dyn dispatch uses it for completeness. Its candidate list comes
//! from impls and the host body's own coercions (`dyn_coercion.rs`), which
//! can miss a type coerced in a callee. A dispatch whose walked arms cover
//! every recorded runtime type for the receiver's trait object needs no
//! blessing for its default arm; any other dispatch fails closed, and a
//! candidate whose body cannot be walked fails closed only when it is a
//! recorded runtime type.
//!
//! The same walk records every function reified to a function pointer, with
//! the fn-pointer type of the cast (`call/fn_ptr_targets.rs` uses it when a
//! pointer's value is not known locally), whether a constant or static holds
//! a function pointer, and which fn-pointer types a transmute produces.
//!
//! Coercions and reifications inside a function the collector abstracts at
//! the stub boundary are not seen; the encoder models those functions by
//! their stubs, not by their bodies.

use crate::kani_middle::loop_contract_reach::LoopContractReach;
use rustc_public::ty::{Binder, ExistentialTraitRef, GenericArgs, TraitDef, Ty};
use std::cell::RefCell;
use std::sync::Arc;

/// One concrete type unsized to a trait object with this principal.
#[derive(Clone, Debug)]
pub(crate) struct DynCoercion {
    pub(crate) principal: TraitDef,
    /// The principal's generic arguments (for `dyn Fn(u8) -> u8`, `(u8,)`).
    pub(crate) args: GenericArgs,
    pub(crate) concrete: Ty,
}

/// Every dyn coercion a harness can reach, and every function it reifies to a
/// function pointer.
#[derive(Clone, Debug, Default)]
pub(crate) struct DynUniverse {
    coercions: Vec<DynCoercion>,
    /// `(operand type, fn-pointer type)` of every `ReifyFnPointer` and
    /// `ClosureFnPointer` cast in a reachable body. The operand is the function
    /// item or closure type.
    fn_ptr_reifications: Vec<(Ty, Ty)>,
    /// A function pointer stored in a constant or static allocation (outside a
    /// vtable). The encoder does not read such a value as the target's id, so
    /// the reification list says nothing about what it holds.
    fn_ptr_in_allocation: bool,
    /// Fn-pointer types a transmute produces: a pointer of such a type may
    /// hold a value no reification at that type made.
    fn_ptr_transmute_targets: Vec<Ty>,
    /// `dyn` → `dyn` unsizes that change the principal (trait upcasting,
    /// `Box<dyn Sub>` → `Box<dyn Super>`), as `(source, target)` principals.
    /// Every runtime type of the source is one of the target's
    /// ([`DynUniverse::close_over_upcasts`]).
    upcasts: Vec<((TraitDef, GenericArgs), (TraitDef, GenericArgs))>,
    /// Target principals of an upcast whose source principal has no recorded
    /// runtime type (its values come from somewhere the collector does not
    /// see, such as a stub): their runtime types are unknown.
    open_principals: Vec<(TraitDef, GenericArgs)>,
    /// Which reachable functions can reach a loop contract, from the same
    /// walk's call graph (design 5, `loop_contract_reach.rs`). `None` until
    /// the collector computed it: a reader then fails closed.
    loop_contract_reach: Option<Arc<LoopContractReach>>,
}

impl DynUniverse {
    /// What the call graph says about reachable loop contracts. `None` when
    /// the collector did not compute it (see the field).
    pub(crate) fn loop_contract_reach(&self) -> Option<Arc<LoopContractReach>> {
        self.loop_contract_reach.clone()
    }

    /// Record the collector's loop-contract reach (`reachability.rs`).
    pub(crate) fn set_loop_contract_reach(&mut self, reach: LoopContractReach) {
        self.loop_contract_reach = Some(Arc::new(reach));
    }

    /// The reified `(operand type, fn-pointer type)` pairs.
    pub(crate) fn fn_ptr_reifications(&self) -> &[(Ty, Ty)] {
        &self.fn_ptr_reifications
    }

    /// Whether some constant or static allocation holds a function pointer.
    pub(crate) fn fn_ptr_in_allocation(&self) -> bool {
        self.fn_ptr_in_allocation
    }

    /// The fn-pointer types some transmute produces.
    pub(crate) fn fn_ptr_transmute_targets(&self) -> &[Ty] {
        &self.fn_ptr_transmute_targets
    }

    fn note(&mut self, concrete: Ty, principal: &Binder<ExistentialTraitRef>) {
        let entry = DynCoercion {
            principal: principal.value.def_id,
            args: principal.value.generic_args.clone(),
            concrete,
        };
        if !self.coercions.iter().any(|seen| {
            seen.principal == entry.principal
                && seen.args == entry.args
                && seen.concrete == entry.concrete
        }) {
            self.coercions.push(entry);
        }
    }

    /// The runtime types a trait object with this principal (and, when
    /// given, these principal arguments) can have.
    pub(crate) fn concrete_types(
        &self,
        principal: TraitDef,
        args: Option<&GenericArgs>,
    ) -> Vec<Ty> {
        let mut types: Vec<Ty> = Vec::new();
        for coercion in &self.coercions {
            if coercion.principal == principal
                && args.is_none_or(|args| *args == coercion.args)
                && !types.contains(&coercion.concrete)
            {
                types.push(coercion.concrete);
            }
        }
        types
    }

    /// Add every runtime type of each upcast's source principal to its target
    /// principal, to a fixpoint (an upcast of an upcast). A `dyn Super` built
    /// from a `dyn Sub` has the `dyn Sub`'s runtime type, and no `Unsize` from
    /// a concrete type to `dyn Super` records it: without this, a merge over
    /// `dyn Super` whose arms cover the directly coerced types counted as
    /// complete, and a lone directly coerced type was walked unconditionally
    /// (`walker_dyn_upcast_dual.rs`).
    fn close_over_upcasts(&mut self) {
        loop {
            let mut added = false;
            for ((src_def, src_args), (dst_def, dst_args)) in self.upcasts.clone() {
                let sources: Vec<Ty> = self
                    .coercions
                    .iter()
                    .filter(|c| c.principal == src_def && c.args == src_args)
                    .map(|c| c.concrete)
                    .collect();
                for concrete in sources {
                    if !self.coercions.iter().any(|c| {
                        c.principal == dst_def && c.args == dst_args && c.concrete == concrete
                    }) {
                        self.coercions.push(DynCoercion {
                            principal: dst_def,
                            args: dst_args.clone(),
                            concrete,
                        });
                        added = true;
                    }
                }
            }
            if !added {
                break;
            }
        }
        for ((src_def, src_args), target) in self.upcasts.clone() {
            let source_known =
                self.coercions.iter().any(|c| c.principal == src_def && c.args == src_args);
            if !source_known && !self.open_principals.contains(&target) {
                self.open_principals.push(target);
            }
        }
    }

    /// Does an upcast from a trait object with no recorded runtime type reach
    /// this principal? Its runtime types are then not all recorded.
    pub(crate) fn is_open(&self, principal: TraitDef, args: &GenericArgs) -> bool {
        self.open_principals.iter().any(|(def, open_args)| *def == principal && open_args == args)
    }

    /// Every principal trait with at least one coercion.
    pub(crate) fn principals(&self) -> Vec<TraitDef> {
        let mut out: Vec<TraitDef> = Vec::new();
        for coercion in &self.coercions {
            if !out.contains(&coercion.principal) {
                out.push(coercion.principal);
            }
        }
        out
    }
}

thread_local! {
    /// The universe under construction while the collector runs.
    static COLLECTING: RefCell<Option<DynUniverse>> = const { RefCell::new(None) };
    /// The universe of the harness being encoded.
    static HARNESS: RefCell<Option<Arc<DynUniverse>>> = const { RefCell::new(None) };
    /// How many vtable allocations the collector is inside.
    static VTABLE_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Start recording coercions (the collector's entry).
pub(crate) fn begin_collection() {
    COLLECTING.with(|cell| *cell.borrow_mut() = Some(DynUniverse::default()));
}

/// Stop recording and return what was recorded.
pub(crate) fn end_collection() -> DynUniverse {
    let mut universe = COLLECTING.with(|cell| cell.borrow_mut().take()).unwrap_or_default();
    universe.close_over_upcasts();
    universe
}

/// Record that `concrete` is unsized to the trait object `principal`
/// describes. A trait object with no principal (`dyn Send`) has no methods to
/// dispatch and is not recorded.
pub(crate) fn note_coercion(concrete: Ty, principal: Option<&Binder<ExistentialTraitRef>>) {
    let Some(principal) = principal else { return };
    COLLECTING.with(|cell| {
        if let Some(universe) = cell.borrow_mut().as_mut() {
            universe.note(concrete, principal);
        }
    });
}

/// Record a `dyn` → `dyn` unsize between these principals. Keeping the
/// principal (dropping an auto trait: `dyn Tr + Send` → `dyn Tr`) adds no
/// runtime type, and a target with no principal (`dyn Send`) has no methods
/// to dispatch.
pub(crate) fn note_dyn_to_dyn(
    source: Option<&Binder<ExistentialTraitRef>>,
    target: Option<&Binder<ExistentialTraitRef>>,
) {
    let (Some(source), Some(target)) = (source, target) else { return };
    let source = (source.value.def_id, source.value.generic_args.clone());
    let target = (target.value.def_id, target.value.generic_args.clone());
    if source == target {
        return;
    }
    COLLECTING.with(|cell| {
        if let Some(universe) = cell.borrow_mut().as_mut()
            && !universe.upcasts.contains(&(source.clone(), target.clone()))
        {
            universe.upcasts.push((source, target));
        }
    });
}

/// Record a `ReifyFnPointer` / `ClosureFnPointer` cast of an operand of type
/// `operand` to the fn-pointer type `target`.
pub(crate) fn note_fn_ptr_reification(operand: Ty, target: Ty) {
    COLLECTING.with(|cell| {
        if let Some(universe) = cell.borrow_mut().as_mut()
            && !universe.fn_ptr_reifications.contains(&(operand, target))
        {
            universe.fn_ptr_reifications.push((operand, target));
        }
    });
}

/// Record a transmute whose result is the fn-pointer type `target`.
pub(crate) fn note_fn_ptr_transmute(target: Ty) {
    COLLECTING.with(|cell| {
        if let Some(universe) = cell.borrow_mut().as_mut()
            && !universe.fn_ptr_transmute_targets.contains(&target)
        {
            universe.fn_ptr_transmute_targets.push(target);
        }
    });
}

/// Record a function pointer found in an allocation, unless the collector is
/// inside a vtable (whose entries are dispatched through `dyn`, not called
/// through a fn pointer).
pub(crate) fn note_fn_ptr_in_allocation() {
    if VTABLE_DEPTH.with(|depth| depth.get()) > 0 {
        return;
    }
    COLLECTING.with(|cell| {
        if let Some(universe) = cell.borrow_mut().as_mut() {
            universe.fn_ptr_in_allocation = true;
        }
    });
}

/// Run `f` with the collector marked as inside a vtable allocation.
pub(crate) fn inside_vtable<T>(f: impl FnOnce() -> T) -> T {
    VTABLE_DEPTH.with(|depth| depth.set(depth.get() + 1));
    let result = f();
    VTABLE_DEPTH.with(|depth| depth.set(depth.get() - 1));
    result
}

/// Installs a harness's universe for the encoder and restores the previous
/// one when dropped.
pub(crate) struct HarnessUniverseGuard {
    previous: Option<Arc<DynUniverse>>,
}

impl HarnessUniverseGuard {
    pub(crate) fn install(universe: Arc<DynUniverse>) -> Self {
        let previous = HARNESS.with(|cell| cell.borrow_mut().replace(universe));
        Self { previous }
    }
}

impl Drop for HarnessUniverseGuard {
    fn drop(&mut self) {
        let previous = self.previous.take();
        HARNESS.with(|cell| *cell.borrow_mut() = previous);
    }
}

/// The universe of the harness being encoded, when the collector ran for it.
/// `None` outside a per-harness codegen (unit tests that encode a body
/// directly): the dyn dispatch then treats every candidate set as possibly
/// incomplete.
pub(crate) fn current_harness_universe() -> Option<Arc<DynUniverse>> {
    HARNESS.with(|cell| cell.borrow().clone())
}
