// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Can an iterator call run a closure whose body carries an obligation?
//!
//! Both lanes stub `Iterator::next` of std's closure adapters (`Map`,
//! `Filter`, `FilterMap`, and `Zip`, `Chain` and `Flatten` over them),
//! `Iterator::collect`, and, in the CHC lane, `Iterator::sum` and
//! `Iterator::fold`. A stub computes, or over-approximates, the VALUE of the
//! call, and none of them runs the closures the real call runs: a `Filter`'s
//! predicate, a `Map`'s function, a `fold`'s accumulator closure when the
//! replay cannot address the sequence. Every panic and every check in those
//! closures was therefore dropped, and nothing stood in for it. Measured
//! (AY alignment round 8, review round 5, all Kani FAILED on the closure's own
//! check, beside a holding assert): in the CHC lane an `Iterator::sum` of
//! `Saturating`, `Wrapping` or `f32` over a `Filter` whose predicate panics,
//! a `fold` over that `Filter`, and a bare `next()` on it were proved clean;
//! in the BMC lane a `next()` on a `Filter`, a `Map` or a `FilterMap` whose
//! closure panics, and a `collect()` of such a `Map`, were proved clean.
//!
//! [`ty_may_run_obligated_closure`] answers the question from the call's Rust
//! types: every closure or function item among the generic arguments of the
//! receiver's type (`Filter<Iter<'_, u8>, {closure}>`, recursively through
//! nested adapters, references and tuples) is walked by the obligation-free
//! walk (`obligation_free_walk`), the same walk the vacuity certificate and
//! the CHC walker's Rule D trust. A closure it cannot certify obligation-free,
//! one it cannot resolve, a function pointer or a trait object counts as one
//! that may panic. The stub then adds a conservative check: a fresh flag
//! alone, reachable whenever the call is, which can never be certified as a
//! real counterexample. Precision is lost only where a closure the call runs
//! has an obligation the walk sights or cannot rule out; a predicate that
//! only compares (`|x| **x > 1`) or calls obligation-free code
//! (`acc.wrapping_add(x)`) costs nothing.

use std::collections::HashSet;

use crate::callee_body::CalleeBody;
use rustc_middle::ty::TyCtxt;
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::ty::{ClosureDef, ClosureKind, GenericArgKind, GenericArgs, RigidTy, Ty, TyKind};

use crate::codegen_ay::obligation_free_walk::{
    StubMap, body_is_transitively_obligation_free_trusting,
};

/// Past this nesting depth a type counts as one that may run an obligated
/// closure: the walk fails closed rather than stopping short.
const MAX_TYPE_DEPTH: usize = 16;

/// The description of the conservative check both lanes add.
pub(in crate::codegen_ay) const UNMODELED_CLOSURE_MESSAGE: &str =
    "Iterator adapter: a closure this call runs is not modelled and may panic";

/// Can a value of type `ty` (an iterator, or a reference to one) run a closure
/// or function whose body may carry an obligation, when an iterator method is
/// called on it? `true` when the answer is not certainly no.
pub(in crate::codegen_ay) fn ty_may_run_obligated_closure(tcx: TyCtxt<'_>, ty: Ty) -> bool {
    walk(tcx, ty, 0, &mut HashSet::new())
}

fn walk(tcx: TyCtxt<'_>, ty: Ty, depth: usize, seen: &mut HashSet<Ty>) -> bool {
    if depth > MAX_TYPE_DEPTH {
        return true;
    }
    if !seen.insert(ty) {
        return false;
    }
    let TyKind::RigidTy(rigid) = ty.kind() else {
        // An alias, parameter or bound type: not a concrete type the walk can
        // read, so fail closed.
        return true;
    };
    match rigid {
        RigidTy::Closure(def, args) => closure_may_carry_obligation(tcx, def, &args),
        RigidTy::FnDef(def, args) => match Instance::resolve(def, &args) {
            Ok(instance) => instance_may_carry_obligation(tcx, instance),
            Err(_) => true,
        },
        RigidTy::Adt(_, args) => generic_args_may_run(tcx, &args, depth, seen),
        RigidTy::Ref(_, inner, _)
        | RigidTy::RawPtr(inner, _)
        | RigidTy::Slice(inner)
        | RigidTy::Array(inner, _) => walk(tcx, inner, depth + 1, seen),
        RigidTy::Tuple(tys) => tys.iter().any(|ty| walk(tcx, *ty, depth + 1, seen)),
        RigidTy::Bool
        | RigidTy::Char
        | RigidTy::Int(_)
        | RigidTy::Uint(_)
        | RigidTy::Float(_)
        | RigidTy::Str
        | RigidTy::Never => false,
        // A function pointer, a trait object, a coroutine, a foreign or
        // pattern type, and any kind this walk does not know: fail closed.
        _ => true,
    }
}

fn generic_args_may_run(
    tcx: TyCtxt<'_>,
    args: &GenericArgs,
    depth: usize,
    seen: &mut HashSet<Ty>,
) -> bool {
    args.0.iter().any(|arg| match arg {
        GenericArgKind::Type(ty) => walk(tcx, *ty, depth + 1, seen),
        _ => false,
    })
}

/// Does the closure `def` instantiated at `args` carry an obligation the walk
/// sights, or one it cannot rule out? An unresolvable closure counts as one.
fn closure_may_carry_obligation(tcx: TyCtxt<'_>, def: ClosureDef, args: &GenericArgs) -> bool {
    [ClosureKind::FnMut, ClosureKind::Fn, ClosureKind::FnOnce]
        .into_iter()
        .find_map(|kind| Instance::resolve_closure(def, args, kind).ok())
        .is_none_or(|instance| instance_may_carry_obligation(tcx, instance))
}

/// The obligation-free walk over `instance` and everything it reaches. It is
/// given no stub map, so a callee a stub would replace is not certified.
fn instance_may_carry_obligation(tcx: TyCtxt<'_>, instance: Instance) -> bool {
    let Some(body) = instance.callee_body() else {
        return true;
    };
    !body_is_transitively_obligation_free_trusting(
        tcx,
        instance,
        &body,
        &StubMap::default(),
        is_total_std_view,
    )
}

/// core's safe functions that turn a valid `&str` or slice into one of its
/// iterators: `str::chars`, `str::bytes`, `str::char_indices`, `<[T]>::iter`,
/// `<[T]>::iter_mut`. Their bodies hold no `Assert` and no panicking call,
/// only the offset sites of building the iterator's end pointer, which hold
/// for every valid argument; a closure that calls nothing else carries no
/// check that can fail. Without this, `flat_map(|s| s.chars())`, which the CHC
/// lane's `FlattenNext` stub models exactly over string literals, lost its
/// proof (`tests/kani/Iterator/flat_map.rs`, measured on the 737 parity units).
fn is_total_std_view(instance: &Instance) -> bool {
    if instance.def.krate().name != "core" {
        return false;
    }
    let name = instance.def.name();
    [
        "core::str::<impl str>::chars",
        "core::str::<impl str>::bytes",
        "core::str::<impl str>::char_indices",
        "core::slice::<impl [T]>::iter",
        "core::slice::<impl [T]>::iter_mut",
    ]
    .contains(&name.as_str())
}
