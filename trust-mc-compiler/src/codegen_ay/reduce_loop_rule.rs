// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! When Kani's unwinding assertion fails on the std loop an iterator
//! reduction (`Iterator::sum`, `Iterator::fold`) runs, under a declared
//! `#[kani::unwind(U)]`, per receiver shape. Shared by the CHC reduction arms
//! (`chc/call/codegen_call_iterator_adapter/`) and the BMC element-wise
//! unroll (`statement/collections/iter_adapters.rs`).
//!
//! Measured on the corpus-rev Kani 4c0fce8c3 with this toolchain's std
//! (walker fail-closed review 6 round 2, findings 1 and 8; N elements under
//! `unwind(U)` at N = U and N = U + 1, recorded in
//! docs/chc-hole-fix-designs-2026-09-24.md, "Walker fail-closed: repair
//! round 2"): the loop fails `unwinding assertion loop 0` exactly when more
//! than `U` elements remain ([`ReduceLoopRule::PassesPastBound`]) for a
//! `slice::Iter` / `slice::IterMut` and `Map`, `Filter`, `Copied`, `Cloned`
//! and `Enumerate` of one (the slice iterator's do-while `fold`); and
//! once `U` elements remain ([`ReduceLoopRule::ReachesBound`]) for an
//! `array::IntoIter` or `vec::IntoIter` (a loop that tests before its
//! body), as for `try_fold`, `rev`, `take` and a `Range`, which are not
//! classified.
//!
//! `Skip<I>` takes `I`'s rule only when `I::nth` runs no loop (a slice
//! iterator, an `array` / `vec` `IntoIter`, and `Copied` / `Enumerate` of
//! one, which delegate `nth`): `Skip::fold` first calls `I::nth`, and for
//! `Map`, `Filter` or `Cloned` that is a loop over the inner elements
//! (`advance_by` / `find`) with its own unwinding assertion (walker
//! fail-closed review 6 round 3; Kani fails `filter(..).skip(1)` and
//! `map(..).skip(6)` over 4 elements under `unwind(4)`).
//!
//! [`iter_sum_is_core_numeric_fold`] decides whether a call of
//! `Iterator::sum` is the numeric fold every reduction model encodes at all.

use rustc_public::CrateDef;
use rustc_public::mir::TerminatorKind;
use rustc_public::mir::mono::Instance;
use rustc_public::ty::{FnDef, GenericArgKind, GenericArgs, RigidTy, Ty, TyKind};

/// When Kani's unwinding assertion fails on a reduction's loop over `R`
/// remaining elements under `#[kani::unwind(U)]`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReduceLoopRule {
    /// `R > U`: the loop body runs before its exit test (do-while).
    PassesPastBound,
    /// `R >= U`: the exit test runs before the body.
    ReachesBound,
}

impl ReduceLoopRule {
    /// Does the loop stay within `unwind` for every `R <= bound`? An unknown
    /// rule (`None`) is read as the stricter [`Self::ReachesBound`].
    pub(crate) fn holds_up_to(rule: Option<Self>, bound: u64, unwind: u64) -> bool {
        match rule {
            Some(Self::PassesPastBound) => bound <= unwind,
            Some(Self::ReachesBound) | None => bound < unwind,
        }
    }

    /// Does the loop fail its unwinding assertion over exactly `remaining`
    /// elements? An unknown rule is read as [`Self::ReachesBound`].
    pub(crate) fn fails_at(rule: Option<Self>, remaining: u64, unwind: u64) -> bool {
        !Self::holds_up_to(rule, remaining, unwind)
    }
}

/// The measured rule of the loop a `sum` / `fold` over a receiver of type
/// `ty` runs, `None` for a shape that was not measured. `ty` must be
/// monomorphic (the caller resolves it against its body).
pub(crate) fn reduce_loop_rule(ty: Ty) -> Option<ReduceLoopRule> {
    rule_of(ty, 0)
}

fn rule_of(ty: Ty, depth: usize) -> Option<ReduceLoopRule> {
    if depth > 8 {
        return None;
    }
    let TyKind::RigidTy(RigidTy::Adt(def, adt_args)) = ty.kind() else {
        return None;
    };
    let name = def.name();
    let last = name.rsplit("::").next().unwrap_or(&name);
    let in_module = |module: &str| name.contains(module);
    match last {
        "Iter" | "IterMut" if in_module("slice") => Some(ReduceLoopRule::PassesPastBound),
        "IntoIter" if in_module("array") || in_module("vec") => Some(ReduceLoopRule::ReachesBound),
        // Adapters whose `fold` hands the whole remaining sequence to the
        // inner iterator's `fold`: the inner rule.
        "Map" | "Filter" | "Copied" | "Cloned" | "Enumerate" if in_module("iter") => {
            rule_of(first_type_arg(&adt_args)?, depth + 1)
        }
        // `Skip::fold` runs `I::nth(n - 1)` before `I::fold`: the inner rule
        // only where that `nth` runs no loop of its own.
        "Skip" if in_module("iter") => {
            let inner = first_type_arg(&adt_args)?;
            if nth_is_loop_free(inner, depth + 1) { rule_of(inner, depth + 1) } else { None }
        }
        _ => None,
    }
}

fn first_type_arg(args: &GenericArgs) -> Option<Ty> {
    args.0.iter().find_map(|arg| match arg {
        GenericArgKind::Type(inner) => Some(*inner),
        _ => None,
    })
}

/// Does `ty::nth` (and the `advance_by` it may call) run no loop? A slice
/// iterator and an `array` / `vec` `IntoIter` step by index arithmetic;
/// `Copied` and `Enumerate` delegate `nth` to their inner iterator. Every
/// other shape (`Map`, `Filter`, `Cloned`, ... use the default `nth`, whose
/// `advance_by` calls `next` in a loop) is `false`.
fn nth_is_loop_free(ty: Ty, depth: usize) -> bool {
    if depth > 8 {
        return false;
    }
    let TyKind::RigidTy(RigidTy::Adt(def, adt_args)) = ty.kind() else {
        return false;
    };
    let name = def.name();
    let last = name.rsplit("::").next().unwrap_or(&name);
    let in_module = |module: &str| name.contains(module);
    match last {
        "Iter" | "IterMut" if in_module("slice") => true,
        "IntoIter" if in_module("array") || in_module("vec") => true,
        "Copied" | "Enumerate" if in_module("iter") => {
            first_type_arg(&adt_args).is_some_and(|inner| nth_is_loop_free(inner, depth + 1))
        }
        _ => false,
    }
}

/// How a call of `Iterator::sum` is modelled, when it is modelled at all
/// ([`iter_sum_model`]): the step each element adds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SumModel {
    /// Core's `Sum` for a primitive integer or float: `+`, with the caller's
    /// overflow check on an integer.
    Checked,
    /// Core's `Sum` for `Wrapping<int>`: `wrapping_add`, no check.
    Wrapping,
    /// Core's `Sum` for `Saturating<int>`: `saturating_add`, no check.
    Saturating {
        /// The wrapped integer's signedness.
        signed: bool,
    },
}

/// The model of a call of `Iterator::sum::<I, S>` (`def` with `args`), or
/// `None` when the call is left to the encoder's ordinary call path. Only
/// core's own impls are modelled: `<S as Sum<I::Item>>::sum` must resolve to
/// core's impl for a primitive integer or float `S` ([`SumModel::Checked`])
/// or for `Wrapping` / `Saturating` of a primitive integer.
///
/// The models were keyed on the method NAME, so every `Sum` impl was read as
/// checked integer addition: a user `impl Sum<&u8> for Mx` (max, first
/// element, a `for` loop), a user `impl Sum<&M> for u8` with a primitive
/// target, and std's `Wrapping` / `Saturating` sums (walker fail-closed
/// review 6 round 3; `tools/soundness-duals/user_sum_impl_dual.rs`).
///
/// Decided on the monomorphic `Iterator::sum` body the call runs (with the
/// unit's stubs applied): its one call of `Sum::sum`, resolved to the impl
/// item. An iterator that overrides `sum`, an unresolvable call, or a body
/// in any other shape is `None`.
pub(crate) fn iter_sum_model(def: FnDef, args: &GenericArgs) -> Option<SumModel> {
    let GenericArgKind::Type(target) = args.0.get(1)? else {
        return None;
    };
    let model = match target.kind() {
        TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Float(_)) => SumModel::Checked,
        TyKind::RigidTy(RigidTy::Adt(adt, adt_args)) => {
            let name = adt.name();
            let in_num = name.starts_with("std::num::") || name.starts_with("core::num::");
            let inner = first_type_arg(&adt_args)?;
            let signed = match inner.kind() {
                TyKind::RigidTy(RigidTy::Int(_)) => true,
                TyKind::RigidTy(RigidTy::Uint(_)) => false,
                _ => return None,
            };
            match name.rsplit("::").next() {
                Some("Wrapping") if in_num => SumModel::Wrapping,
                Some("Saturating") if in_num => SumModel::Saturating { signed },
                _ => return None,
            }
        }
        _ => return None,
    };
    let sum_impl = resolved_sum_impl(def, args)?;
    let krate = sum_impl.def.krate();
    (!krate.is_local && krate.name == "core").then_some(model)
}

/// Is a call of `Iterator::sum` modelled at all ([`iter_sum_model`])?
pub(crate) fn iter_sum_is_core_numeric_fold(def: FnDef, args: &GenericArgs) -> bool {
    iter_sum_model(def, args).is_some()
}

/// The `<S as Sum<A>>::sum` impl item a call of `Iterator::sum` (`def` with
/// `args`) runs: the one call in the monomorphic body, resolved. `None` for a
/// body in any other shape.
fn resolved_sum_impl(def: FnDef, args: &GenericArgs) -> Option<Instance> {
    use crate::callee_body::CalleeBody;
    let instance = Instance::resolve(def, args).ok()?;
    let body = instance.callee_body()?;
    let mut sum_impl = None;
    for block in &body.blocks {
        let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
            continue;
        };
        let TyKind::RigidTy(RigidTy::FnDef(callee, callee_args)) = func.ty(body.locals()).ok()?.kind()
        else {
            return None;
        };
        if !callee.name().ends_with("Sum::sum") || sum_impl.is_some() {
            return None;
        }
        sum_impl = Some(Instance::resolve(callee, &callee_args).ok()?);
    }
    sum_impl
}

/// Does `instance`'s body run exactly one call, of `Iterator::fold`? The
/// shape of a `Sum` impl that is a fold over its argument (`Mx(it.fold(..))`).
fn body_runs_one_fold(instance: &Instance) -> bool {
    use crate::callee_body::CalleeBody;
    let Some(body) = instance.callee_body() else {
        return false;
    };
    let mut folds = 0;
    for block in &body.blocks {
        let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
            continue;
        };
        let Ok(func_ty) = func.ty(body.locals()) else {
            return false;
        };
        match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(callee, _)) if callee.name().ends_with("Iterator::fold") => {
                folds += 1;
            }
            _ => return false,
        }
    }
    folds == 1
}

fn is_library_crate(name: &str) -> bool {
    matches!(name, "core" | "alloc" | "std")
}

/// Is `instance` a step of an `Iterator::sum` the harness inliner inlines
/// even under an abstracted prefix (`std::slice::` names every function
/// instantiated with a slice iterator)? Exact either way: inlining runs the
/// same code. It exposes a `Sum` impl whose body is one `Iterator::fold`
/// call (outside core, alloc and std) to the encoders' reduction models,
/// which replay a fold's closure step by step; the walker has no reduction
/// model and would fail closed on it. `Iterator::sum` itself when the call
/// is not modelled ([`iter_sum_model`]) and its impl has that shape, and the
/// impl item.
pub(crate) fn is_inlined_sum_instance(instance: &Instance) -> bool {
    let def_name = instance.def.name();
    if def_name == "std::iter::Iterator::sum" || def_name == "core::iter::Iterator::sum" {
        let TyKind::RigidTy(RigidTy::FnDef(def, args)) = instance.ty().kind() else {
            return false;
        };
        return iter_sum_model(def, &args).is_none()
            && resolved_sum_impl(def, &args).is_some_and(|sum_impl| {
                !is_library_crate(&sum_impl.def.krate().name) && body_runs_one_fold(&sum_impl)
            });
    }
    is_sum_impl_item(&def_name)
        && !is_library_crate(&instance.def.krate().name)
        && body_runs_one_fold(instance)
}

/// Is `def_name` an impl item `<S as std::iter::Sum<A>>::sum`?
fn is_sum_impl_item(def_name: &str) -> bool {
    def_name.starts_with('<')
        && def_name.split_once(" as ").is_some_and(|(_, tail)| {
            (tail.starts_with("std::iter::Sum") || tail.starts_with("core::iter::Sum"))
                && tail.ends_with(">::sum")
        })
}

/// [`iter_sum_model`] for a call operand read against `locals` (the body the
/// operand belongs to).
pub(crate) fn iter_sum_call_model(
    func: &rustc_public::mir::Operand,
    locals: &[rustc_public::mir::LocalDecl],
) -> Option<SumModel> {
    let TyKind::RigidTy(RigidTy::FnDef(def, args)) = func.ty(locals).ok()?.kind() else {
        return None;
    };
    iter_sum_model(def, &args)
}

/// [`iter_sum_is_core_numeric_fold`] for a call operand read against
/// `locals`.
pub(crate) fn iter_sum_call_is_core_numeric_fold(
    func: &rustc_public::mir::Operand,
    locals: &[rustc_public::mir::LocalDecl],
) -> bool {
    iter_sum_call_model(func, locals).is_some()
}

/// Is `ty`, the source of a `Vec` `extend` / `spec_extend`, one the extend
/// models read exactly: a slice, array or `Vec` (or a reference to one), a
/// slice iterator, an `array` / `vec` `IntoIter`, a `Range` /
/// `RangeInclusive`, or `Copied` / `Cloned` of one of those?
///
/// The models read the length (and, for a constant slice or a range, the
/// values) of the underlying sequence; they never run an adapter's closure
/// and never drop or reorder an element. `v.extend(a.iter().map(|x| {
/// assert!(*x < 200); *x }))` verified clean on the BMC lane where Kani fails,
/// and on the CHC lane only an unrelated demotion kept it from proving
/// (walker fail-closed repair round 4, finding 8's class,
/// `r2_closure_more.rs` `c05_extend_map_bug`); a `Filter` or `Take` source
/// would have extended by the unfiltered length. Any other source is not
/// modelled (the callers fail closed).
pub(crate) fn extend_source_is_modelled(ty: Ty) -> bool {
    extend_source_is_modelled_at(ty, 0)
}

fn extend_source_is_modelled_at(ty: Ty, depth: usize) -> bool {
    if depth > 8 {
        return false;
    }
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => extend_source_is_modelled_at(inner, depth + 1),
        TyKind::RigidTy(RigidTy::Array(..) | RigidTy::Slice(_)) => true,
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            let name = def.name();
            let last = name.rsplit("::").next().unwrap_or(&name);
            let in_module = |module: &str| name.contains(module);
            match last {
                "Vec" if in_module("vec") => true,
                "Iter" | "IterMut" if in_module("slice") => true,
                "IntoIter" if in_module("array") || in_module("vec") => true,
                "Range" | "RangeInclusive" if in_module("ops") => true,
                "Copied" | "Cloned" if in_module("iter") => first_type_arg(&args)
                    .is_some_and(|inner| extend_source_is_modelled_at(inner, depth + 1)),
                _ => false,
            }
        }
        _ => false,
    }
}
