// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Native model of `kani::vec::any_vec::<T, N>` and `kani::vec::exact_vec::<T, N>`.
//!
//! Both library bodies build their Vec through `Box::new(any())`, `<[T]>::into_vec`,
//! `truncate` and `shrink_to_fit`, i.e. through RawVecInner / Layout internals the
//! walker cannot inline. Each un-inlined call became a fresh symbol
//! (`nested_call_overapprox`), which blocked certification of every counterexample
//! downstream (the out-of-bounds `get_unchecked(len)` Kani expects to fail included).
//!
//! The model states exactly the library's contract and nothing more:
//! - `exact_vec::<T, N>`: `len == cap == N`.
//! - `any_vec::<T, N>`:  `len == cap`, `len <= N` (the library asserts
//!   `capacity() == len()` after `shrink_to_fit`, and `vec![]` has `cap == 0`).
//! - elements: a fresh array (every `T` value Kani's `Arbitrary` may produce is
//!   admitted; element types with validity invariants are declined, see
//!   `element_admits_every_bit_pattern`).
//! - buffer: a fresh heap object marked provably valid, so `Vec::drop` and
//!   pointer checks resolve against real provenance.
//!
//! DRAFT — to be placed in trust-mc-compiler/src/codegen_ay/chc/call/.

use crate::codegen_ay::chc::codegen_ctx::{ExactVar, Havoc};
use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, Sort};
use rustc_public::mir::Operand;
use rustc_public::ty::{AdtKind, GenericArgKind, RigidTy, Ty, TyKind};
use tracing::debug;

use crate::codegen_ay::chc::call::call_accumulator::CallAccumulator;
use crate::codegen_ay::names::vec_layout;
use crate::codegen_ay::types::{CtorFieldExt, POINTER_WIDTH, ptr_sort};

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_call_vec_ops::ProjectedVecState;
use super::codegen_ctx::globals::chc_fresh_name;
use super::codegen_ctx::types::CollectionProjectionKind;
use super::codegen_rules::CodegenRules;

/// Which Kani vector generator a call names.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) enum KaniVecCtor {
    /// `kani::vec::any_vec::<T, N>` — `len <= N`.
    Any,
    /// `kani::vec::exact_vec::<T, N>` — `len == N`.
    Exact,
    /// `<Vec<T> as kani::BoundedArbitrary>::bounded_any::<N>` — `len <= N`,
    /// `cap == N`: the library builds `Vec::from([T; N])` (capacity N) and
    /// `truncate`s it to a length `kani::any_where(|l| l <= N)`.
    BoundedAny,
}

/// Leading path of Kani's `BoundedArbitrary` impls for std containers, as the
/// MIR inline pass and the stub lookup print them.
const BOUNDED_ANY_IMPL_PREFIX: &str = "kani::bounded_arbitrary::<impl kani::BoundedArbitrary for ";

/// Whether an instance name (generics included) is Kani's
/// `BoundedArbitrary::bounded_any` for `Vec<T>`, which the CHC lane models
/// natively (`bounded_any_call`). The MIR inline pass must keep these calls:
/// their bodies build the value through `Vec::from([T; N])`, `truncate` and
/// `as_mut_ptr`, which the walker havocs, and the raw-pointer arguments of
/// those havocked calls trip the fail-closed
/// `inline_nested_call_writes_through_pointer` net (ledger row 72,
/// `bounded-arbitrary/{option,result}`).
///
/// `String` is NOT modeled: the lane's `Vec`/`String` drop is a no-op
/// (`StubKind::VecDrop`), so a model-built `String` made `drop(s); *s.as_ptr()`
/// a clean proof where Kani reports a use after free, and the library body it
/// replaced had failed that harness (T4a review, 2026-09-24). It keeps the
/// library body until the drop invalidates the buffer.
pub(in crate::codegen_ay) fn is_bounded_any_ctor_name(name: &str) -> bool {
    let Some(rest) = name.strip_prefix(BOUNDED_ANY_IMPL_PREFIX) else {
        return false;
    };
    let self_ty_ok = ["std::vec::Vec<", "alloc::vec::Vec<"].iter().any(|p| rest.starts_with(p));
    let Some(pos) = rest.rfind(">::bounded_any") else {
        return false;
    };
    let tail = &rest[pos + ">::bounded_any".len()..];
    // Nothing after the method but its own `::<N>`: a trailing
    // `::{closure#0}` names the generator's closure, not the generator.
    self_ty_ok
        && (tail.is_empty()
            || (tail.starts_with("::<") && tail.ends_with('>') && !tail.contains('{')))
}

/// What a `bounded_any` call builds.
#[derive(Clone, Copy, Debug)]
pub(in crate::codegen_ay) enum BoundedAnyTarget {
    /// `Vec<T>`, with its element type.
    Vec(Ty),
}

fn adt_path_is(ty: Ty, paths: &[&str]) -> Option<rustc_public::ty::GenericArgs> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            use rustc_public::CrateDef;
            let name = def.name();
            paths.iter().any(|p| name == *p).then_some(args)
        }
        _ => None,
    }
}

/// Recognise `<Vec<T> as kani::BoundedArbitrary>::bounded_any::<N>` (the trait
/// method, or Kani's resolved impl method) whose result is `dest_ty`, and
/// return what it builds and `N`.
///
/// The destination type decides the target: Kani implements the trait for
/// `Vec<T>` itself, and coherence rules out any other impl for it, so a
/// `bounded_any` returning a `Vec` is Kani's. A `String` result is not
/// recognised (see `is_bounded_any_ctor_name`).
pub(in crate::codegen_ay) fn bounded_any_call(
    func: &Operand,
    locals: &[rustc_public::mir::LocalDecl],
    dest_ty: Ty,
) -> Option<(BoundedAnyTarget, u64)> {
    let func_ty = func.ty(locals).ok()?;
    let TyKind::RigidTy(RigidTy::FnDef(def, args)) = func_ty.kind() else {
        return None;
    };
    let name = def.0.name();
    let is_trait_method = name == "kani::BoundedArbitrary::bounded_any";
    let is_impl_method =
        name.starts_with(BOUNDED_ANY_IMPL_PREFIX) && name.ends_with(">::bounded_any");
    if !is_trait_method && !is_impl_method {
        return None;
    }
    let bound = args.0.iter().rev().find_map(|arg| match arg {
        GenericArgKind::Const(c) => c.eval_target_usize().ok(),
        _ => None,
    })?;
    let vec_args = adt_path_is(dest_ty, &["std::vec::Vec", "alloc::vec::Vec"])?;
    let elem = vec_args.0.iter().find_map(|arg| match arg {
        GenericArgKind::Type(t) => Some(*t),
        _ => None,
    })?;
    Some((BoundedAnyTarget::Vec(elem), bound))
}

/// Whether the `bounded_any` model represents a `Vec<T>` EXACTLY: `T` is
/// `bool` (its `Bool` sort has exactly two values) or a builtin scalar (or a
/// tuple / array of them), and `T` is not zero-sized. The model accepts only
/// these element types; any other keeps the library body (and its fail-closed
/// nets).
///
/// Each exclusion is a behaviour of the library body the model leaves out:
/// - a zero-sized `T`: std reports `Vec::<T>::capacity() == usize::MAX`, not
///   the `N` the model states (`()` passes `element_is_builtin_arbitrary`
///   vacuously, `[u8; 0]` passes it too);
/// - a user type, even an unconstrained `#[derive(kani::Arbitrary)]`: the
///   body is `Vec::from([T; N])` then `truncate(len)`, and `truncate` runs
///   `T`'s `Drop` on the cut elements, which the model never does; and the
///   derive check (`arbitrary_is_unconstrained_derive`) only inspects the calls
///   of `T::any()`, so a hand-written impl that restricts values by arithmetic
///   or panics inside `any()` would pass as exact (T4a review, 2026-09-24:
///   false proofs and false Genuine certificates on both).
/// Builtin scalars have no drop glue and no user `Arbitrary`.
pub(in crate::codegen_ay) fn bounded_any_element_is_exact(ty: Ty) -> bool {
    (matches!(ty.kind(), TyKind::RigidTy(RigidTy::Bool)) || element_is_builtin_arbitrary(ty))
        && builtin_element_is_sized_nonzero(ty)
}

/// For a type `bounded_any_element_is_exact` otherwise admits (`bool`,
/// builtin scalars and tuples / arrays of them): whether it occupies at least
/// one byte. `false` for `()`, `[T; 0]`, a tuple of only such, and anything
/// whose array length does not evaluate (fail-closed).
fn builtin_element_is_sized_nonzero(ty: Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Bool | RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Float(_)) => {
            true
        }
        TyKind::RigidTy(RigidTy::Tuple(tys)) => {
            tys.iter().any(|t| builtin_element_is_sized_nonzero(*t))
        }
        TyKind::RigidTy(RigidTy::Array(inner, len)) => {
            len.eval_target_usize().is_ok_and(|n| n > 0) && builtin_element_is_sized_nonzero(inner)
        }
        _ => false,
    }
}

/// Length of a `bounded_any::<N>` result: every value in `0..=N` and nothing
/// else. A fresh `f` folded to `ite(f <= N, f, N)` needs no side constraint,
/// so the same term serves the walker (which returns only a value) and the
/// harness-level rule.
pub(in crate::codegen_ay::chc) fn bounded_any_len(bound: u64) -> Expr {
    let n = Expr::bitvec_const(bound, POINTER_WIDTH);
    if bound == 0 {
        return n;
    }
    let fresh = ExactVar::nondet(chc_fresh_name("kani_bounded_any_len"), ptr_sort());
    Expr::ite(fresh.clone().bvule(n.clone()), fresh, n)
}

/// The value `bounded_any::<N>` returns, as a term of `dest_sort` (the `Vec`
/// datatype): a fresh heap object marked provably valid, `len` in `0..=N`,
/// `cap` `N` (`Vec::from([T; N])` then `truncate`), and a fresh data array
/// where the sort carries one — together with its length term. `None` for an
/// element type the model does not represent exactly, or a sort it does not
/// recognise.
pub(in crate::codegen_ay::chc) fn bounded_any_value(
    ctx: &mut ChcCtx<'_, '_>,
    target: BoundedAnyTarget,
    bound: u64,
    dest_sort: &Sort,
) -> Option<(Expr, Expr)> {
    let BoundedAnyTarget::Vec(elem) = target;
    if !bounded_any_element_is_exact(elem) {
        return None;
    }
    let dt = dest_sort.datatype_sort()?;
    let ctor = dt.constructors.first()?;
    let has = |name: &str| ctor.fields.iter().any(|f| f.name == name);
    if !(has(vec_layout::FLD_PTR) && has(vec_layout::FLD_LEN) && has(vec_layout::FLD_CAP)) {
        return None;
    }
    let len = bounded_any_len(bound);
    let cap = Expr::bitvec_const(bound, POINTER_WIDTH);
    let obj_id = ctx.heap_state.next_heap_alloc_id()?;
    ctx.heap_state.record_heap_alloc_size(obj_id, 0);
    ctx.heap_state.mark_provably_valid_backing(obj_id);
    let ptr = Expr::bitvec_const(i128::from(obj_id), 32).concat(Expr::bitvec_const(0u64, 32));
    let mut fields = Vec::with_capacity(ctor.fields.len());
    for field in &ctor.fields {
        let value = match field.name.as_str() {
            vec_layout::FLD_PTR => ptr.clone(),
            vec_layout::FLD_LEN => len.clone(),
            vec_layout::FLD_CAP => cap.clone(),
            vec_layout::FLD_DATA if field.sort.array_sort().is_some() => {
                ExactVar::nondet(chc_fresh_name("kani_bounded_any_data"), field.sort.clone())
            }
            _ => return None,
        };
        fields.push(value);
    }
    let value = Expr::datatype_constructor(
        dt.name.clone(),
        crate::codegen_ay::names::cons_name(&dt.name),
        fields,
        dest_sort.clone(),
    );
    Some((value, len))
}

/// Whether a resolved instance name (generics included, e.g.
/// `kani::vec::any_vec::<isize, 0>`) names a Kani vector generator. Used by the
/// MIR inline pass, which sees instance names rather than `FnDef`s.
pub(in crate::codegen_ay) fn is_kani_vec_ctor_name(name: &str) -> bool {
    ["kani::vec::any_vec", "kani::vec::exact_vec"].iter().any(|path| {
        name.strip_prefix(path).is_some_and(|rest| {
            rest.is_empty()
                // `::<T, N>` generics with nothing after them: a trailing
                // `::{closure#0}` names the generator's closure instead.
                || (rest.starts_with("::<") && rest.ends_with('>') && !rest.contains("}"))
        })
    })
}

/// Recognise `kani::vec::{any_vec, exact_vec}::<T, N>` and return `(ctor, T, N)`.
///
/// Matches the callee's `FnDef` path exactly, so a user function that merely
/// shares the method name does not qualify.
pub(in crate::codegen_ay) fn kani_vec_ctor_call(
    func: &Operand,
    locals: &[rustc_public::mir::LocalDecl],
) -> Option<(KaniVecCtor, Ty, u64)> {
    let func_ty = func.ty(locals).ok()?;
    let TyKind::RigidTy(RigidTy::FnDef(def, args)) = func_ty.kind() else {
        return None;
    };
    let ctor = match def.0.name().as_str() {
        "kani::vec::any_vec" => KaniVecCtor::Any,
        "kani::vec::exact_vec" => KaniVecCtor::Exact,
        _ => return None,
    };
    let mut elem = None;
    let mut bound = None;
    for arg in &args.0 {
        match arg {
            GenericArgKind::Type(t) if elem.is_none() => elem = Some(*t),
            GenericArgKind::Const(c) if bound.is_none() => {
                bound = c.eval_target_usize().ok();
            }
            _ => {}
        }
    }
    Some((ctor, elem?, bound?))
}

/// Whether Kani's `Arbitrary` for `ty` can only be the unconstrained builtin:
/// integers and floats, and tuples / arrays built from them. Any other element
/// type (user structs, enums, `bool`, `char`, references) may carry an
/// `Arbitrary` impl or a validity invariant that restricts the value set.
pub(in crate::codegen_ay) fn element_is_builtin_arbitrary(ty: Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Float(_)) => true,
        TyKind::RigidTy(RigidTy::Tuple(tys)) => {
            tys.iter().all(|t| element_is_builtin_arbitrary(*t))
        }
        TyKind::RigidTy(RigidTy::Array(inner, _)) => element_is_builtin_arbitrary(inner),
        _ => false,
    }
}

/// Whether `<ty as kani::Arbitrary>::any` is the body `#[derive(kani::Arbitrary)]`
/// generates WITHOUT `#[safety_constraint]`: every call in it is `kani::any::<F>`
/// for a builtin-arbitrary `F`, and nothing else (no `kani::assume`, no
/// `is_safe()`, no user code). Such an impl admits exactly every field value,
/// so a fresh element array is EXACT, not an over-approximation.
///
/// Resolution mirrors `kani_middle::implements_arbitrary`: resolve
/// `kani::any::<ty>`, follow its single `T::any()` call to the impl instance,
/// then scan that body. Any failure to resolve answers `false` (keep the
/// over-approximation marker — fail-closed).
pub(in crate::codegen_ay) fn arbitrary_is_unconstrained_derive(ty: Ty) -> bool {
    use crate::callee_body::CalleeBody;
    use crate::kani_middle::kani_functions::{find_kani_functions, try_kani_function_from_fn_def};
    use rustc_public::mir::TerminatorKind;
    use rustc_public::mir::mono::Instance;
    use rustc_public::ty::GenericArgs;
    use trust_mc_kani_types::kani_functions::{KaniFunction, KaniModel};

    if !matches!(ty.kind(), TyKind::RigidTy(RigidTy::Adt(def, _)) if def.kind() == AdtKind::Struct)
    {
        return false;
    }
    let is_kani_any = |def: rustc_public::ty::FnDef| {
        try_kani_function_from_fn_def(def) == Some(KaniFunction::Model(KaniModel::Any))
    };
    let Some(kani_any) = find_kani_functions().get(&KaniFunction::Model(KaniModel::Any)).copied()
    else {
        return false;
    };
    let Ok(any_instance) =
        Instance::resolve(kani_any, &GenericArgs(vec![GenericArgKind::Type(ty)]))
    else {
        return false;
    };
    let Some(any_body) = any_instance.callee_body() else {
        return false;
    };
    // `kani::any::<T>()` is `T::any()`: its one call is the impl's `any`.
    let mut impl_calls = any_body.blocks.iter().filter_map(|bb| match &bb.terminator.kind {
        TerminatorKind::Call { func, .. } => match func.ty(any_body.locals()).ok()?.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, args)) => Some((def, args)),
            _ => None,
        },
        _ => None,
    });
    let (Some((impl_def, impl_args)), None) = (impl_calls.next(), impl_calls.next()) else {
        return false;
    };
    let Ok(impl_instance) = Instance::resolve(impl_def, &impl_args) else {
        return false;
    };
    let Some(impl_body) = impl_instance.callee_body() else {
        return false;
    };
    let mut saw_field_any = false;
    for bb in &impl_body.blocks {
        let TerminatorKind::Call { func, .. } = &bb.terminator.kind else {
            continue;
        };
        let Some(TyKind::RigidTy(RigidTy::FnDef(def, args))) =
            func.ty(impl_body.locals()).ok().map(|t| t.kind())
        else {
            return false;
        };
        let field_is_builtin = args
            .0
            .iter()
            .any(|a| matches!(a, GenericArgKind::Type(t) if element_is_builtin_arbitrary(*t)));
        if !(is_kani_any(def) && field_is_builtin) {
            return false;
        }
        saw_field_any = true;
    }
    saw_field_any
}

/// Whether a fresh element array is at least as permissive as Kani's
/// `Arbitrary` for `ty` (every value of `ty` is admitted). True for builtin
/// scalars and for plain structs/tuples/arrays of such; false for enums,
/// unions, `bool`, `char`, references and pointers, whose valid values are a
/// strict subset of the bit patterns the array sort can hold.
pub(in crate::codegen_ay) fn element_array_over_approximates(ty: Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Float(_)) => true,
        TyKind::RigidTy(RigidTy::Tuple(tys)) => {
            tys.iter().all(|t| element_array_over_approximates(*t))
        }
        TyKind::RigidTy(RigidTy::Array(inner, _)) => element_array_over_approximates(inner),
        TyKind::RigidTy(RigidTy::Adt(def, args)) if def.kind() == AdtKind::Struct => {
            def.variants().first().is_some_and(|v| {
                v.fields().iter().all(|f| {
                    mono_ty::field_ty(f, &args).is_some_and(element_array_over_approximates)
                })
            })
        }
        _ => false,
    }
}

/// Extension trait: CHC call-terminator route for the Kani vector generators.
pub(in crate::codegen_ay::chc) trait CallKaniAnyVec {
    /// Returns `true` when the call was a Kani vector generator and its rule
    /// has been emitted; `false` leaves the call to the rest of the chain.
    fn try_dispatch_kani_vec_ctor(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallKaniAnyVec for ChcCtx<'tcx, 'body> {
    fn try_dispatch_kani_vec_ctor(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let dest_ty = self.body.locals()[dcx.destination.local].ty;
        let Some((ctor, elem_ty, bound)) = kani_vec_ctor_call(dcx.func, self.body.locals())
            .or_else(|| {
                let (BoundedAnyTarget::Vec(elem), bound) =
                    bounded_any_call(dcx.func, self.body.locals(), dest_ty)?;
                Some((KaniVecCtor::BoundedAny, elem, bound))
            })
        else {
            return false;
        };
        // Only element types whose every value a fresh array admits; others
        // keep the pre-existing inline/fallback lane (fail-closed as before).
        // `bounded_any` goes further and takes only element types the array
        // represents EXACTLY (it records no element approximation).
        let admitted = match ctor {
            KaniVecCtor::BoundedAny => bounded_any_element_is_exact(elem_ty),
            KaniVecCtor::Any | KaniVecCtor::Exact => element_array_over_approximates(elem_ty),
        };
        if !admitted {
            debug!(?ctor, "kani vec ctor: element type has a validity invariant — declined");
            return false;
        }
        let Some(target) = *dcx.target else {
            return false;
        };
        let dest_local = dcx.destination.local;
        if !dcx.destination.projection.is_empty() {
            return false;
        }
        let Some(dest_vec_idx) = self.try_state_idx_for_local(dest_local) else {
            return false;
        };
        // The elements come from `kani::any::<[T; N]>()`, whose `any_array`
        // loop this model does not run (`shared::kani_any_loops`).
        self.kani_any_passes_unwinding_check(
            dcx,
            crate::codegen_ay::shared::kani_any_loops::kani_any_array_loop_passes(elem_ty, bound),
        );

        let mut constraints: Vec<Expr> = Vec::new();
        let mut dests: Vec<usize> = Vec::new();

        // Length: exact N, or a fresh value in [0, N].
        let n = Expr::bitvec_const(bound, POINTER_WIDTH);
        let len = match ctor {
            // `len <= 0` IS `len == 0`: state the constant, as `Vec::new` does.
            // A fresh length pinned by a constraint made PDR re-derive it
            // through every later push (kani/Vectors/any/push_slow.rs timed
            // out on all 15 obligations where the constant proves at once).
            KaniVecCtor::Exact | KaniVecCtor::Any | KaniVecCtor::BoundedAny if bound == 0 => n,
            KaniVecCtor::Exact => n,
            KaniVecCtor::Any | KaniVecCtor::BoundedAny => {
                let len = ExactVar::nondet(chc_fresh_name("kani_any_vec_len"), ptr_sort());
                constraints.push(len.clone().bvule(n));
                len
            }
        };
        // Capacity equals length: exact_vec is `<[T]>::into_vec(Box<[T; N]>)`,
        // any_vec is `vec![]` (cap 0) or truncate + shrink_to_fit, after which
        // the library itself asserts `capacity() == len()`. bounded_any keeps
        // the `Vec::from([T; N])` capacity through `truncate`: exactly N.
        let cap = match ctor {
            KaniVecCtor::BoundedAny => Expr::bitvec_const(bound, POINTER_WIDTH),
            KaniVecCtor::Any | KaniVecCtor::Exact => len.clone(),
        };

        // Buffer: a fresh heap object, provably valid, offset 0.
        let Some(obj_id) = self.heap_state.next_heap_alloc_id() else {
            return false;
        };
        self.heap_state.record_heap_alloc_size(obj_id, 0);
        self.heap_state.mark_provably_valid_backing(obj_id);
        let ptr = Expr::bitvec_const(i128::from(obj_id), 32).concat(Expr::bitvec_const(0u64, 32));

        let projected = self.collections.projection_locals.get(&dest_local).copied()
            == Some(CollectionProjectionKind::Vec);
        let data_sort: Option<Sort> = if projected {
            self.state_var_mgr
                .output_state_vars
                .get(dest_vec_idx + vec_layout::IDX_DATA)
                .map(|(_, s)| s.clone())
        } else {
            self.state_var_mgr.output_state_vars.get(dest_vec_idx).and_then(|(_, s)| {
                s.datatype_sort()?.constructors.first()?.field_sort(vec_layout::FLD_DATA)
            })
        };
        let Some(data_sort) = data_sort.filter(|s| s.array_sort().is_some()) else {
            return false;
        };
        let data_name = chc_fresh_name("kani_any_vec_data");
        let data = if bound == 0 {
            // No element is readable in a zero-length Vec, so the data array is
            // unobservable until a push stores into it. Use `Vec::new`'s shape
            // (a constant array over one fresh default, #4287) — exact here, and
            // the shape the push / index lanes are tuned for.
            let Some(elem_sort) = data_sort.array_sort().map(|a| a.element_sort.clone()) else {
                return false;
            };
            Expr::const_array(ptr_sort(), ExactVar::unobserved(data_name.clone(), elem_sort))
        } else if ctor != KaniVecCtor::BoundedAny
            && !element_is_builtin_arbitrary(elem_ty)
            && !arbitrary_is_unconstrained_derive(elem_ty)
        {
            // A user `Arbitrary` may restrict element values; the fresh array
            // admits them all. Name the freed variable so a counterexample is
            // refused certification only when it actually reads an element.
            let booked = self.record_sound_fallback_reason_identified(
                "kani_vec_elem_arbitrary_overapprox",
                Some(data_name.as_str()),
            );
            Havoc::booked(booked, data_name.clone(), data_sort)
        } else {
            // Every element is the builtin (or an unconstrained derived)
            // `kani::any`: the fresh array is exactly the program's values.
            ExactVar::nondet(data_name.clone(), data_sort)
        };

        if let Some(len_var) = self.collections.len_state.get_len_var(dest_local).cloned() {
            self.collection_len_set(
                &len_var,
                len.clone(),
                &mut CallAccumulator::new(&mut constraints, &mut dests),
            );
        }
        if let Some(cap_var) = self.collections.len_state.get_cap_var(dest_local).cloned() {
            self.collection_cap_set(
                &cap_var,
                cap.clone(),
                &mut CallAccumulator::new(&mut constraints, &mut dests),
            );
        }
        Self::emit_cap_ge_len(cap.clone(), len.clone(), &mut constraints);

        let written = if projected {
            self.constrain_projected_vec_fields_for_call(
                dest_local,
                ProjectedVecState { ptr, len, cap, data },
                &mut constraints,
                &mut dests,
            )
        } else if let Some((out_name, out_sort)) =
            self.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned()
            && let Some(dt_name) = out_sort.datatype_name()
        {
            constraints.push(Self::build_vec_datatype_eq(
                dt_name,
                vec![ptr, len, cap, data],
                &out_name,
                &out_sort,
            ));
            dests.push(dest_local);
            true
        } else {
            false
        };
        if !written {
            // Nothing was constrained: let the ordinary chain handle the call.
            return false;
        }

        debug!(?ctor, bound, dest_local, obj_id, "kani vec ctor: native Vec model");
        let output_args = self.build_output_args(dcx.modified_locals, &dests);
        self.emit_goto_rule_extra(
            dcx.from_app,
            target,
            &output_args,
            dcx.stmt_constraints,
            constraints,
        );
        true
    }
}

#[cfg(test)]
mod tests {
    use super::is_kani_vec_ctor_name;

    #[test]
    fn instance_names_of_the_generators_match() {
        assert!(is_kani_vec_ctor_name("kani::vec::any_vec"));
        assert!(is_kani_vec_ctor_name("kani::vec::exact_vec"));
        assert!(is_kani_vec_ctor_name("kani::vec::any_vec::<isize, 0>"));
        assert!(is_kani_vec_ctor_name("kani::vec::exact_vec::<Dummy, 17>"));
    }

    #[test]
    fn lookalike_names_do_not_match() {
        // A different function in the same module sharing the prefix.
        assert!(!is_kani_vec_ctor_name("kani::vec::any_vec_of_vec"));
        assert!(!is_kani_vec_ctor_name("kani::vec::exact_vec_zst::<u8, 2>"));
        // The generator's own closure is not the generator.
        assert!(!is_kani_vec_ctor_name("kani::vec::any_vec::<isize, 0>::{closure#0}"));
        // A user function that merely shares the method name.
        assert!(!is_kani_vec_ctor_name("my_crate::vec::any_vec::<u8, 4>"));
        assert!(!is_kani_vec_ctor_name("any_vec"));
    }
}
