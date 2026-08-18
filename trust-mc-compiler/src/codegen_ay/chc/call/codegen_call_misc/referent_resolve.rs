// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Referent resolution helpers: resolve_bare_local, resolve_ref_or_const_referent, resolve_raw_eq_referent.
//! Part of #2408 S1: codegen_call_misc decomposition.

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::Operand;
use rustc_public::rustc_internal;
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::{HashMap, HashSet};
use tracing::{debug, warn};

use super::super::ChcCtx;
use super::CallMisc;
use super::dyn_wrapper_restore::peel_pointer_like_dyn_wrapper_expr;
use crate::codegen_ay::chc::codegen_types::CodegenTypes;
use crate::codegen_ay::provenance::{Val, mir_ty_denotes_address};
use crate::codegen_ay::ptr_repr::PtrSlot;
use crate::codegen_ay::types::{
    CtorFieldExt, POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe, ptr_sort,
};
use std::sync::Arc;

/// What a referent resolution actually produced.
///
/// `resolve_ref_or_const_referent` has six tiers and they are NOT
/// interchangeable: the first five resolve *through* the reference and hand
/// back the referent's datum, the last two hand back the operand's own term.
/// This enum is that distinction, carried instead of re-derived — see
/// [`ChcCtx::resolve_ref_or_const_referent_tagged`] for why the width test it
/// replaces could never have decided it.
#[derive(Clone, Debug)]
pub(in crate::codegen_ay::chc) enum Referent {
    /// The REFERENT's own datum: a tier that dereferenced (`ref_targets`,
    /// `const_ref_values`, `const_ref_discriminants`, the static seeds, the
    /// arg-pointee state variables, a decoded fixed-array view), or a by-value
    /// operand whose MIR type is not an address.
    Value(Val),
    /// The operand's OWN translated term, with no report of what it is. For a
    /// reference-typed operand this is the POINTER, not the referent; for
    /// anything else it may be either. Produced by
    /// `translate_operand_with_modified` / `resolve_bare_local`, which serve
    /// every operand in the encoder and report nothing (§4 item 10).
    Unreported(Expr),
}

impl Referent {
    /// Collapses back to a bare `Expr` for consumers that have not been
    /// converted. Every caller of this is an unfinished §4 item 10.
    pub(in crate::codegen_ay::chc) fn into_expr(self) -> Expr {
        match self {
            Self::Value(val) => val.into_expr(),
            Self::Unreported(expr) => expr,
        }
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn resolve_static_seeded_ref_operand(
        &mut self,
        arg: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let (Operand::Copy(place) | Operand::Move(place)) = arg else {
            return None;
        };
        if !place.projection.is_empty() {
            return None;
        }

        let ref_target = self.ref_resolution.ref_targets.get(&place.local)?.clone();
        if !matches!(ref_target.projections.first(), Some(rustc_public::mir::ProjectionElem::Deref))
        {
            return None;
        }

        let static_local = ref_target.local;
        let &static_vec_idx = self.ref_resolution.static_ref_to_state_idx.get(&static_local)?;
        if self.ref_resolution.mutable_static_state_idxs.contains(&static_vec_idx) {
            return None;
        }

        let target_place = rustc_public::mir::Place {
            local: static_local,
            projection: ref_target.projections.clone(),
        };
        let target_ty = target_place.ty(self.body.locals()).ok()?;
        if matches!(target_ty.kind(), TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..))) {
            return None;
        }

        let seed_expr = self.ref_resolution.static_ref_value_seeds.get(&static_vec_idx)?.clone();
        let remaining_projections = &ref_target.projections[1..];
        if remaining_projections.is_empty() {
            return Some(seed_expr);
        }

        let pointee_ty = Self::deref_ref_ty(self.body.locals()[static_local].ty).0;
        self.translate_place_field_index(
            remaining_projections,
            seed_expr,
            Some(pointee_ty),
            modified_locals,
        )
    }

    fn operand_local_is_ref_like(&self, arg: &Operand) -> bool {
        let place = match arg {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => return false,
        };
        if !place.projection.is_empty() {
            return false;
        }
        matches!(
            self.body.locals().get(place.local).map(|decl| decl.ty.kind()),
            Some(TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..)))
        )
    }

    fn try_restore_dyn_trait_referent(&mut self, arg: &Operand, expr: &Expr) -> Option<Expr> {
        if let ExprValue::DatatypeSelector { selector_name, expr: inner, .. } = expr.value()
            && selector_name == "fld_ptr"
            && let Some(dt) = inner.sort().datatype_sort()
            && dt
                .constructors
                .first()
                .is_some_and(|constructor| constructor.has_field("fld_vtable"))
        {
            return Some(inner.clone());
        }

        let (Operand::Copy(place) | Operand::Move(place)) = arg else {
            return None;
        };

        let local_ty = self.body.locals()[place.local].ty;
        if let Some(restored_wrapper_inner) = peel_pointer_like_dyn_wrapper_expr(local_ty, expr) {
            return Some(restored_wrapper_inner);
        }

        if !place.projection.is_empty()
            || expr.sort().bitvec_width() != Some(crate::codegen_ay::types::POINTER_WIDTH)
        {
            return None;
        }

        let vtable_expr = self.known_vtable_expr_for_local(place.local)?;
        self.resolve_unique_wrapped_dyn_vtable_id(local_ty)?;

        let dyn_name = crate::codegen_ay::names::dyn_sort_name("Trait");
        let dyn_sort = crate::codegen_ay::names::struct_sort(
            dyn_name.clone(),
            [("fld_ptr", ptr_sort()), ("fld_vtable", ptr_sort())],
        );
        self.declare_datatype_sort_if_needed(&dyn_sort);
        let ctor_name = {
            let mut s = String::with_capacity(dyn_name.len() + 3);
            s.push_str(&dyn_name);
            s.push_str("_mk");
            s
        };
        Some(Expr::datatype_constructor(
            &dyn_name,
            &ctor_name,
            vec![expr.clone(), vtable_expr],
            dyn_sort,
        ))
    }

    fn fixed_array_view_sort_for_ty(&self, ty: rustc_public::ty::Ty) -> Option<Sort> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => {
                self.fixed_array_view_sort_for_ty(pointee)
            }
            TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => {
                self.fixed_array_view_sort_for_ty(pointee)
            }
            TyKind::RigidTy(RigidTy::Array(..)) => Self::translate_ty(ty),
            TyKind::RigidTy(RigidTy::Adt(adt_def, args))
                if rustc_internal::internal(self.tcx, ty).is_simd() =>
            {
                let variants = adt_def.variants();
                if variants.len() != 1 || variants[0].fields().len() != 1 {
                    return None;
                }
                let field_ty = variants[0].fields()[0].ty_with_args(&args);
                matches!(field_ty.kind(), TyKind::RigidTy(RigidTy::Array(..)))
                    .then(|| Self::translate_ty(field_ty))
                    .flatten()
            }
            _ => None,
        }
    }

    /// Rebuild a `[T; N]` referent by LOADING it, when the resolved expression
    /// is an address rather than the referent's bytes.
    ///
    /// `reinterpret_fixed_layout_expr`'s BV→Array case is a pure *bit view*: it
    /// slices the 8 bytes of a BV64 into array elements. That is correct when
    /// the BV64 holds the referent's data and catastrophically wrong when it
    /// holds the referent's ADDRESS — the array then contains
    /// `[obj_id, offset]` bytes instead of the pointee, so e.g.
    /// `transmute::<&str, &[u8]>("Rust") == &[82, 117, 115, 116]` compares
    /// `b"Rust"` against `[0, 0, 0, 0]` and reports a bogus counterexample.
    ///
    /// The value-vs-address distinction is made EXPLICITLY here rather than by
    /// another width heuristic:
    ///
    /// * `try_extract_constant_addr` is a *structural* test. It only succeeds on
    ///   `concat(obj_id: bv32 const, offset: bv32 const)`, the exact shape the
    ///   split-pointer model emits for an address. A BV64 that merely happens to
    ///   be 8 bytes wide (a genuine flattened `[u8; 8]` value, an arithmetic
    ///   result, a state variable) does not match it.
    /// * The Rust type must additionally peel a reference/raw pointer, so a bare
    ///   `[T; N]` local whose value is carried flattened in a BV is untouched.
    ///
    /// Both conditions together mean the expression provably carries pointer
    /// provenance, so the array is rebuilt from `N` per-element loads.
    ///
    /// The load MUST go through the ELEMENT type key (`u8` for `[u8; 4]`), not
    /// the array/slice key: promoted constants and ordinary stores seed memory
    /// byte-wise under the element key, so `load_from_memory`'s multi-element
    /// reconstruction — which keys by the *array* type (`slice_u8`) — reads an
    /// array nothing was ever written to and yields unconstrained slots. This is
    /// the same key `try_raw_eq_array`'s Tier 2 memory path already uses.
    fn try_load_fixed_array_referent_from_address(
        &mut self,
        local_ty: rustc_public::ty::Ty,
        addr: &Expr,
        target_sort: &Sort,
    ) -> Option<Expr> {
        // Structural proof that `addr` is an address, not data.
        Self::try_extract_constant_addr(addr)?;

        // ... and that the Rust type agrees: `&[T; N]` / `*const [T; N]`.
        let (pointee_ty, peeled) = Self::deref_ref_ty(local_ty);
        if !peeled {
            return None;
        }
        let TyKind::RigidTy(RigidTy::Array(elem_ty, len_const)) = pointee_ty.kind() else {
            return None;
        };
        let array_len = len_const.eval_target_usize().ok()? as usize;
        // Same element-wise budget `try_raw_eq_array` uses; keeps formulas bounded.
        if array_len == 0 || array_len > 256 {
            return None;
        }

        let arr_sort = target_sort.array_sort()?;
        let idx_width = arr_sort.index_sort.bitvec_width()?;
        let elem_sort = arr_sort.element_sort.clone();
        let elem_width = elem_sort.bitvec_width()?;
        let elem_bytes = self.get_type_size(elem_ty)? as u64;
        let type_key = self.type_key_for_body_ty(elem_ty).into_owned();

        let base = coerce_bitvec_width_safe(addr.clone(), POINTER_WIDTH, SignExtension::ZeroExtend);
        let mut result =
            Expr::const_array(Sort::bitvec(idx_width), Expr::bitvec_const(0u64, elem_width));
        for i in 0..array_len {
            let offset = Expr::bitvec_const((i as u64) * elem_bytes, POINTER_WIDTH);
            let elem_addr = base.clone().bvadd(offset);
            let loaded =
                self.load_from_type_array(elem_addr, &type_key, elem_sort.clone(), None)?;
            let loaded = coerce_bitvec_width_safe(loaded, elem_width, SignExtension::ZeroExtend);
            result = result.store(Expr::bitvec_const(i as u64, idx_width), loaded);
        }

        if result.sort() != target_sort {
            return None;
        }
        debug!(
            fn_name = %self.fn_name,
            array_len,
            elem_type = %type_key,
            "CHC: fixed-array referent arrived as an address; loaded from memory instead of reinterpreting"
        );
        Some(result)
    }

    fn try_reinterpret_fixed_array_view_referent(
        &mut self,
        arg: &Operand,
        expr: &Expr,
    ) -> Option<Expr> {
        let (Operand::Copy(place) | Operand::Move(place)) = arg else {
            return None;
        };
        if !place.projection.is_empty() {
            return None;
        }
        let local_ty = self.body.locals()[place.local].ty;
        let target_sort = self.fixed_array_view_sort_for_ty(local_ty)?;
        // An address must be dereferenced, never bit-sliced. This runs BEFORE
        // the width guard below, which only rejects arrays too WIDE for the
        // pointer — `[u8; 4]` fits inside 8 pointer bytes and would otherwise be
        // silently fabricated out of `obj_id`/`offset` bits.
        if let Some(loaded) =
            self.try_load_fixed_array_referent_from_address(local_ty, expr, &target_sort)
        {
            return Some(loaded);
        }
        // Guard: do not reinterpret a BV pointer as an array when the Rust
        // array's total byte width exceeds the BV width. For example,
        // &[u8; 65] resolves to a BV64 pointer — reinterpreting 8 pointer
        // bytes as 65 data bytes produces a bogus comparison. Part of #1739.
        if let Some(src_bv_width) = expr.sort().bitvec_width() {
            if let Some(array_byte_count) = self.rust_array_byte_count(local_ty) {
                if array_byte_count * 8 > src_bv_width as usize {
                    return None;
                }
            }
        }
        Self::reinterpret_fixed_layout_expr(expr, &target_sort)
    }

    /// Extract the total byte count of a Rust fixed-size array type.
    ///
    /// For `[T; N]` (possibly behind references/raw pointers), returns
    /// `Some(N * size_of(T))`. Returns `None` for non-array types or if
    /// the length/element size cannot be determined at compile time.
    fn rust_array_byte_count(&self, ty: rustc_public::ty::Ty) -> Option<usize> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
            | TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => self.rust_array_byte_count(pointee),
            TyKind::RigidTy(RigidTy::Array(elem_ty, len_const)) => {
                let n = len_const.eval_target_usize().ok()? as usize;
                let elem_bytes = self.get_type_size(elem_ty)?;
                Some(n * elem_bytes)
            }
            _ => None,
        }
    }

    /// Look up a bare local's state variable for Copy/Move operands without projection.
    /// Used as a last-resort fallback when ref_targets and translate_operand both fail.
    /// Handles cases where &T reference locals have state variables representing the
    /// referent value (e.g., references created via inline transforms).
    pub(in crate::codegen_ay::chc) fn resolve_bare_local_impl(
        arg: &Operand,
        state_vars: &[(Arc<str>, Sort)],
        output_state_vars: &[(Arc<str>, Sort)],
        modified_locals: &HashSet<usize>,
        local_to_state_idx: &HashMap<usize, usize>,
        fn_name: &str,
    ) -> Option<Expr> {
        if let Operand::Copy(place) | Operand::Move(place) = arg
            && place.projection.is_empty()
        {
            let local_idx: usize = place.local;
            let vec_idx = if let Some(vec_idx) = local_to_state_idx.get(&local_idx).copied() {
                vec_idx
            } else {
                // Fail-closed: identity fallback is unsound when collect_state_vars
                // flattens compound types (Option, Result, tuples, structs), causing
                // MIR local indices to diverge from state vector indices. See #2698.
                warn!(
                    fn_name,
                    local_idx,
                    state_vars_len = state_vars.len(),
                    output_state_vars_len = output_state_vars.len(),
                    "CHC missing local_to_state_idx entry; returning None (identity fallback removed per #2698/#2709)"
                );
                return None;
            };
            let (name, sort) = if modified_locals.contains(&local_idx) {
                output_state_vars.get(vec_idx)?
            } else {
                state_vars.get(vec_idx)?
            };
            return Some(Expr::var(&**name, sort.clone()));
        }
        None
    }

    /// Resolve a call operand to its referent value through tracked refs + const refs.
    ///
    /// Tier order:
    /// 1. `resolve_ref_operand` through `ref_targets`
    /// 2. `const_ref_values` for promoted scalar/array refs
    /// 3. `const_ref_discriminants` for promoted unit-enum refs (`Ordering`, etc.)
    ///    3.5 `static_ref_value_seeds` for immutable statics routed through
    ///    `static_ref_to_state_idx`
    /// 4. `ref_arg_pointee_idx` for function parameter references (#2979)
    /// 5. `translate_operand_with_modified`
    /// 6. `resolve_bare_local` fallback
    ///
    /// Part of #1739: primitive cmp must resolve `&Ordering::Equal` and similar
    /// const-ref arguments to avoid unconstrained compare fallbacks.
    pub(in crate::codegen_ay::chc) fn resolve_ref_or_const_referent_impl(
        &mut self,
        arg: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        self.resolve_ref_or_const_referent_tagged(arg, modified_locals).map(Referent::into_expr)
    }

    /// [`Self::resolve_ref_or_const_referent_impl`], reporting WHICH KIND of
    /// term it produced.
    ///
    /// # The fact this adds, and the guess it retires
    ///
    /// The tier list above is not a list of equivalent fallbacks. Tiers 1–4.5
    /// resolve *through* the reference and hand back the REFERENT's datum;
    /// tiers 5–6 hand back the operand's own translated term, which for a
    /// reference-typed operand is the POINTER. Collapsed to a bare `Expr` those
    /// two are indistinguishable at `POINTER_WIDTH`, and consumers were left to
    /// re-derive the difference from a width test — `codegen_call_atomic`'s
    /// load partition being the one the census kept flagging, since an
    /// `AtomicUsize` datum is `bv64` exactly like the address of one.
    ///
    /// That framing was wrong in a way worth stating: the undecidable question
    /// ("does this `AtomicUsize` hold a pointer bit-pattern or an integer?") is
    /// not the question the consumer needs answered. The consumer needs to know
    /// **which tier answered**, and that is not a run-time property at all — it
    /// is known here, at the producer, and was simply dropped. No `AtomicCell`
    /// tag written by the last store is required, and none could have helped:
    /// `store_forward_map` records the store's DECLARED type key, which is
    /// `usize` in both readings.
    ///
    /// [`Referent::Unreported`] is not a claim that the term IS an address — it
    /// is the honest statement that `translate_operand_with_modified` /
    /// `resolve_bare_local` report nothing (§4 item 10, the same wall the two
    /// `#[deprecated]` `*_untyped` memory shims are parked against).
    pub(in crate::codegen_ay::chc) fn resolve_ref_or_const_referent_tagged(
        &mut self,
        arg: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Referent> {
        // Part of #4044: by-value call operands must preserve value semantics.
        // Running them through the ref/const-ref lanes can accidentally treat a
        // plain local as a referent when ref-tracking metadata is present from a
        // prior `&mut` call in the same body, which corrupts same-arg by-value
        // calls like `assert_rows_bits_distinct(row, row)`.
        if !self.operand_local_is_ref_like(arg) {
            // `operand_local_is_ref_like` is false for a projected place and for
            // a constant too, so "not ref-like" does not by itself mean "not a
            // pointer". The MIR type of the operand decides which it is, via the
            // campaign's own whitelist: a non-address type means this term is
            // the datum; an address type means it is the operand's own pointer
            // and nothing here resolved through it.
            let by_value_is_datum = !arg
                .ty(self.body.locals())
                .ok()
                .map(|ty| self.resolve_body_ty(ty))
                .is_some_and(mir_ty_denotes_address);
            let tag = |expr: Expr| {
                if by_value_is_datum {
                    Referent::Value(Val::of_value(expr))
                } else {
                    Referent::Unreported(expr)
                }
            };
            if let Some(expr) = self.translate_operand_with_modified(arg, modified_locals) {
                if let Some(array_view) = self.try_reinterpret_fixed_array_view_referent(arg, &expr)
                {
                    // A decoded fixed-array view IS the referent's storage image.
                    return Some(Referent::Value(Val::of_value(array_view)));
                }
                if let Some(dyn_referent) = self.try_restore_dyn_trait_referent(arg, &expr) {
                    return Some(tag(dyn_referent));
                }
                return Some(tag(expr));
            }
            return Self::resolve_bare_local(
                arg,
                &self.state_var_mgr.state_vars,
                &self.state_var_mgr.output_state_vars,
                modified_locals,
                &self.state_var_mgr.local_to_state_idx,
                &self.fn_name,
            )
            .map(tag);
        }

        // Tiers 1 .. 4.5 all resolve THROUGH the reference, so everything they
        // return is the referent's own datum: `Referent::Value`.
        //
        // NOTE: the `?` operators inside them abort the WHOLE resolution, as
        // they always have — a tier that applies and then fails to find its
        // state variable does NOT fall through to tier 5. That is why this is
        // one function and not two: splitting it would silently convert those
        // aborts into unreported operand translations.
        // Tier 1: ref_targets — resolves &local patterns.
        // Prefer immutable static-backed seeds when the referent is a concrete
        // non-pointer value derived from a tracked static local.
        if let Some(expr) = self.resolve_static_seeded_ref_operand(arg, modified_locals) {
            if let Some(array_view) = self.try_reinterpret_fixed_array_view_referent(arg, &expr) {
                return Some(Referent::Value(Val::of_value(array_view)));
            }
            if let Some(dyn_referent) = self.try_restore_dyn_trait_referent(arg, &expr) {
                return Some(Referent::Value(Val::of_value(dyn_referent)));
            }
            return Some(Referent::Value(Val::of_value(expr)));
        }

        // Tier 1a: authoritative promoted-constant referent. A `_N = &CONST`
        // promoted reference has its referent value decoded byte-exact into
        // `const_ref_values`, keyed by the ref local itself. This MUST be
        // preferred over the generic ref_targets path (Tier 1b) below: for a
        // promoted const the ref_targets chain resolves the synthetic promoted
        // local to its POINTER ADDRESS and then coerces that address into the
        // referent sort via `unflatten_bitvec_to_datatype` — reading the enum
        // tag out of pointer bits (e.g. `Some(4)` whose address is
        // `concat(obj_id, 0)` unflattens to `None`). Taking the decoded value
        // here keeps an enum-literal referent (`Some(4)`) bit-compatible with
        // the array-element-read flatten it is compared against in derived
        // `PartialEq::eq`, so `a[i] == Some(4)` is provable when true.
        if let Operand::Copy(place) | Operand::Move(place) = arg
            && place.projection.is_empty()
            && let Some(expr) = self.ref_resolution.const_ref_values.get(&place.local).cloned()
        {
            if let Some(array_view) = self.try_reinterpret_fixed_array_view_referent(arg, &expr) {
                return Some(Referent::Value(Val::of_value(array_view)));
            }
            return Some(Referent::Value(Val::of_value(expr)));
        }

        // Tier 1b: generic tracked ref_targets path.
        if let Some(expr) = self.resolve_ref_operand(arg, modified_locals) {
            if let Some(array_view) = self.try_reinterpret_fixed_array_view_referent(arg, &expr) {
                return Some(Referent::Value(Val::of_value(array_view)));
            }
            if let Some(dyn_referent) = self.try_restore_dyn_trait_referent(arg, &expr) {
                return Some(Referent::Value(Val::of_value(dyn_referent)));
            }
            // Part of #4101: when the ref_target's local has a `const_ref_values`
            // entry (e.g. seeded by SIMD `as_array` dispatch), prefer it. Without
            // this, `raw_eq` on `as_array()` results sees BV64 pointers instead of
            // the underlying Array expressions.
            //
            // Address-vs-value: this used to read "when Tier 1b resolves to a BV64
            // POINTER", i.e. it declared the term an address purely because it was
            // 64 bits wide. Nothing here establishes that — `resolve_ref_operand`
            // returns the ref_target's own term and reports nothing about whether
            // that term is the pointer or the referent's datum, and at
            // `POINTER_WIDTH` the two are indistinguishable. The claim is dropped,
            // and the substitution does not need it: `const_ref_values` holds the
            // byte-exact DECODED referent of a promoted constant, which is
            // authoritative for the referent either way — if the Tier 1b term is
            // the address, it is the wrong thing to return here; if it is already
            // the referent's datum, the decoded constant denotes the same referent
            // and is the form Tier 1a documents as the one that stays bit-compatible
            // with the comparison it feeds.
            //
            // What is left is a SHAPE test, and that is all it is: `PtrSlot::Thin`
            // accepts exactly the `== Some(64)` this replaces, keeping the override
            // scoped to the #4101 shape rather than firing on every tracked ref.
            // It is NOT evidence of addresshood and no `Loc` is minted from it.
            // Deciding the underlying question needs a provenance-REPORTING operand
            // translator (§4 item 10); until then the scope limiter stays.
            if matches!(PtrSlot::of_sort(expr.sort()), Some(PtrSlot::Thin)) {
                if let Operand::Copy(p) | Operand::Move(p) = arg {
                    if p.projection.is_empty() {
                        // Follow ref_targets to find the target local, then check const_ref_values.
                        if let Some(rt) = self.ref_resolution.ref_targets.get(&p.local) {
                            if let Some(const_val) =
                                self.ref_resolution.const_ref_values.get(&rt.local)
                            {
                                return Some(Referent::Value(Val::of_value(const_val.clone())));
                            }
                        }
                    }
                    let ty = self.body.locals().get(p.local).map(|d| format!("{:?}", d.ty));
                    warn!(
                        local = p.local,
                        ?ty,
                        proj_empty = p.projection.is_empty(),
                        "[#3806 referent] Tier 1: sort=BV64"
                    );
                }
            }
            return Some(Referent::Value(Val::of_value(expr)));
        }
        // Tier 2: const_ref_values — resolves promoted constant references
        // (arrays, scalars) that ref_targets cannot track.
        if let Operand::Copy(place) | Operand::Move(place) = arg
            && place.projection.is_empty()
            && let Some(expr) = self.ref_resolution.const_ref_values.get(&place.local).cloned()
        {
            if let Some(array_view) = self.try_reinterpret_fixed_array_view_referent(arg, &expr) {
                return Some(Referent::Value(Val::of_value(array_view)));
            }
            return Some(Referent::Value(Val::of_value(expr)));
        }
        // Tier 3: const_ref_discriminants — resolves promoted unit-enum refs.
        if let Operand::Copy(place) | Operand::Move(place) = arg
            && place.projection.is_empty()
            && let Some(discriminant) =
                self.ref_resolution.const_ref_discriminants.get(&place.local)
        {
            return Some(Referent::Value(Val::of_value(Expr::bitvec_const(
                *discriminant as i128,
                32,
            ))));
        }
        // Tier 3.5: immutable static-backed referent seeds.
        // These preserve array/slice referent values for locals routed through
        // `static_ref_to_state_idx`, including copied/reborrowed aliases that did
        // not originate directly from the constant assignment statement.
        if let Operand::Copy(place) | Operand::Move(place) = arg
            && place.projection.is_empty()
            && let Some(&static_vec_idx) =
                self.ref_resolution.static_ref_to_state_idx.get(&place.local)
            && let Some(expr) =
                self.ref_resolution.static_ref_value_seeds.get(&static_vec_idx).cloned()
        {
            if let Some(array_view) = self.try_reinterpret_fixed_array_view_referent(arg, &expr) {
                return Some(Referent::Value(Val::of_value(array_view)));
            }
            if let Some(dyn_referent) = self.try_restore_dyn_trait_referent(arg, &expr) {
                return Some(Referent::Value(Val::of_value(dyn_referent)));
            }
            return Some(Referent::Value(Val::of_value(expr)));
        }
        // Tier 4: argument reference pointee state variables (Part of #2979).
        // Function parameters with type &T/&mut T have no `_N = &_M` in MIR,
        // so ref_targets has no entry. When raw_eq or other intrinsics are
        // compiled as separate functions rather than inlined, the arguments are
        // these parameters. ref_arg_pointee_idx maps the argument local to the
        // auxiliary pointee state variable that carries the referent value.
        if let Operand::Copy(place) | Operand::Move(place) = arg
            && place.projection.is_empty()
            && let Some(&pointee_vec_idx) =
                self.ref_resolution.ref_arg_pointee_idx.get(&place.local)
        {
            // Use the same SSA-chaining logic as resolve_arg_ref_deref (#2844):
            // 1. local_expr_env for intra-block write-then-read
            // 2. output state var if modified in this block
            // 3. input state var otherwise
            let track_key = usize::MAX - pointee_vec_idx;
            let pointee_expr = if let Some(env_expr) = self.encode.local_expr_env.get(&track_key) {
                debug!(
                    local_idx = place.local,
                    pointee_vec_idx, "CHC: resolve_referent via arg pointee local_expr_env (#2979)"
                );
                env_expr.clone()
            } else if self.encode.modified_state_indices.contains(&pointee_vec_idx) {
                let (out_name, out_sort) =
                    self.state_var_mgr.output_state_vars.get(pointee_vec_idx)?;
                debug!(
                    local_idx = place.local,
                    pointee_vec_idx,
                    "CHC: resolve_referent via arg pointee output state var (#2979)"
                );
                Expr::var(&**out_name, out_sort.clone())
            } else {
                let (in_name, in_sort) = self.state_var_mgr.state_vars.get(pointee_vec_idx)?;
                debug!(
                    local_idx = place.local,
                    pointee_vec_idx,
                    "CHC: resolve_referent via arg pointee input state var (#2979)"
                );
                Expr::var(&**in_name, in_sort.clone())
            };
            if let Some(array_view) =
                self.try_reinterpret_fixed_array_view_referent(arg, &pointee_expr)
            {
                return Some(Referent::Value(Val::of_value(array_view)));
            }
            return Some(Referent::Value(Val::of_value(pointee_expr)));
        }
        // Tier 4.5: pointer locals derived from argument reference deref chains
        // (Part of #3596). Handles `as_array`/`into_array` patterns where a raw
        // pointer is created from `&raw const (*self)`, cast to a different pointer
        // type (e.g., *const [T; N]), then dereferenced. Since argument references
        // are not seeded in ref_targets (Part of #2496), the normal Tier 1
        // propagation can't follow these chains. ptr_deref_to_arg_pointee bridges
        // the gap by tracking which pointer locals derive from arg ref pointees.
        if let Operand::Copy(place) | Operand::Move(place) = arg
            && place.projection.is_empty()
            && let Some(&pointee_vec_idx) =
                self.ref_resolution.ptr_deref_to_arg_pointee.get(&place.local)
        {
            let track_key = usize::MAX - pointee_vec_idx;
            let pointee_expr = if let Some(env_expr) = self.encode.local_expr_env.get(&track_key) {
                debug!(
                    local_idx = place.local,
                    pointee_vec_idx,
                    "CHC: resolve_referent via ptr_deref_to_arg_pointee local_expr_env (#3596)"
                );
                env_expr.clone()
            } else if self.encode.modified_state_indices.contains(&pointee_vec_idx) {
                let (out_name, out_sort) =
                    self.state_var_mgr.output_state_vars.get(pointee_vec_idx)?;
                debug!(
                    local_idx = place.local,
                    pointee_vec_idx,
                    "CHC: resolve_referent via ptr_deref_to_arg_pointee output (#3596)"
                );
                Expr::var(&**out_name, out_sort.clone())
            } else {
                let (in_name, in_sort) = self.state_var_mgr.state_vars.get(pointee_vec_idx)?;
                debug!(
                    local_idx = place.local,
                    pointee_vec_idx,
                    "CHC: resolve_referent via ptr_deref_to_arg_pointee input (#3596)"
                );
                Expr::var(&**in_name, in_sort.clone())
            };
            if let Some(array_view) =
                self.try_reinterpret_fixed_array_view_referent(arg, &pointee_expr)
            {
                return Some(Referent::Value(Val::of_value(array_view)));
            }
            return Some(Referent::Value(Val::of_value(pointee_expr)));
        }
        // Tiers 5 and 6 hand back the operand's OWN term — for a reference
        // operand that is the pointer, not the referent — and report nothing
        // about it: `Referent::Unreported`.
        // Tier 5: direct operand translation (may return pointer BV for refs)
        if let Some(expr) = self.translate_operand_with_modified(arg, modified_locals) {
            if let Some(array_view) = self.try_reinterpret_fixed_array_view_referent(arg, &expr) {
                return Some(Referent::Unreported(array_view));
            }
            if let Some(dyn_referent) = self.try_restore_dyn_trait_referent(arg, &expr) {
                return Some(Referent::Unreported(dyn_referent));
            }
            return Some(Referent::Unreported(expr));
        }
        // Tier 6: bare local state variable
        Self::resolve_bare_local(
            arg,
            &self.state_var_mgr.state_vars,
            &self.state_var_mgr.output_state_vars,
            modified_locals,
            &self.state_var_mgr.local_to_state_idx,
            &self.fn_name,
        )
        .map(Referent::Unreported)
    }
}
// Array-chain resolution + raw_eq referent moved to referent_resolve_chain.rs per #4206.
