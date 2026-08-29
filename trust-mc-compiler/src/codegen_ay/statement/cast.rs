// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//! Type cast codegen for AY - Part of #1354.

use ay_bindings::Expr;
use ay_bindings::SortInner;
use rustc_abi::VariantIdx as InternalVariantIdx;
use rustc_public::mir::Operand;
use rustc_public::rustc_internal;
use rustc_public::ty::{AdtKind, RigidTy, TyKind};
use tracing::{debug, warn};

use super::{IntoOption, PointerCoercion, StatementCodegen};
use crate::codegen_ay::types::SignExtension;
use crate::codegen_ay::types::{
    POINTER_WIDTH, coerce_datatype_structural, construct_dyn_fat_pointer, int_sort,
    int_ty_to_bitvec_width, uint_ty_to_bitvec_width,
};
use crate::rustc_public::CrateDef;

// DT→BV cast handler moved to cast_dt_to_bv.rs per #4206.
use super::cast_dt_to_bv::EnumDiscrInfo;
// DT→DT fallback handler for aggressive field coercion (Part of #3192).
use super::cast_dt_to_dt::coerce_dt_to_dt_fallback;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// For single-field struct wrappers, return signedness of the wrapped field.
    /// Used to preserve sign on DT widening casts for transparent newtypes.
    fn single_field_adt_signedness(ty: &rustc_public::ty::Ty) -> Option<bool> {
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
            return None;
        };
        if def.kind() != AdtKind::Struct {
            return None;
        }
        let variants = def.variants();
        let variant = variants.first()?;
        let fields = variant.fields();
        let field = fields.first()?;
        let field_ty = Self::resolve_generic_ty(field.ty(), &args)?;
        Self::ty_signedness(field_ty)
    }

    /// Cast dispatch that preserves `CastKind` for handlers that need it.
    ///
    /// Part of #3809: `CastKind::Transmute` has a dedicated layout-checked
    /// path instead of falling through the generic DT→DT structural coercion.
    pub(super) fn codegen_cast_with_kind(
        &mut self,
        kind: &super::CastKind,
        operand: &Operand,
        target_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        // Entry trace, not a diagnostic: this fires on EVERY cast, and `a as u64`
        // is not something to warn a user about. At warn! it reached the default
        // output, so any real crate printed a line per cast between the harness
        // name and its verdict.
        debug!(?kind, "ENTRY codegen_cast_with_kind");
        // Part of #3809: Transmute gets a dedicated handler that checks
        // rustc layout compatibility before allowing DT→DT structural coercion.
        // Part of #3192: Subtype is handled identically to Transmute, matching
        // Kani upstream (kani rvalue.rs:797 handles both in a single arm).
        // Subtype casts are used for lifetime/variance coercions where the
        // types are structurally identical.
        if matches!(kind, super::CastKind::Transmute | super::CastKind::Subtype) {
            return self.codegen_transmute_cast(operand, target_ty);
        }
        // Part of #3848/#3793: PointerCoercion::Unsize gets a dedicated wrapper-walk
        // path that constructs fat pointers at the leaf instead of relying on generic
        // structural coercion. Without this, Box<closure> → Box<dyn FnOnce()> fails
        // because the field count changes (thin → fat pointer).
        if let super::CastKind::PointerCoercion(super::PointerCoercion::Unsize) = kind {
            let src_ty = operand.ty(self.body.locals()).into_option();
            if let Some(result) = self.codegen_unsize_cast(operand, src_ty, target_ty) {
                return Some(result);
            }
        }
        // ReifyFnPointer/ClosureFnPointer casts: produce a unique BV64 constant
        // representing the fn pointer identity. Without this, codegen_cast returns
        // None (fn pointer types have no AY sort), leaving the destination
        // unconstrained and causing false CTREX. The actual call dispatch is
        // handled separately at the terminator level by try_codegen_fn_ptr_call.
        // Cross-port from CHC translate_reify_fn_pointer (cast_dispatch.rs:329).
        if let super::CastKind::PointerCoercion(
            PointerCoercion::ReifyFnPointer | PointerCoercion::ClosureFnPointer(_),
        ) = kind
        {
            return Some(self.codegen_reify_fn_pointer(operand));
        }
        // Part of #3192: ArrayToPointer coercion (&[T; N] → *const T / *mut T).
        // In the pointer-based memory model, both &[T; N] and *const T are
        // pointer-width BVs pointing to the same address — the cast is an
        // identity at the BV level. Explicitly handle this to match the CHC
        // path (cast_dispatch.rs:73) and prevent sort-mismatch None returns
        // when the operand resolves to an Array sort.
        if let super::CastKind::PointerCoercion(
            PointerCoercion::ArrayToPointer
            | PointerCoercion::MutToConstPointer
            | PointerCoercion::UnsafeFnPointer,
        ) = kind
        {
            return self.codegen_array_to_pointer_cast(operand, target_ty);
        }
        self.codegen_cast(operand, target_ty)
    }

    /// Translate ReifyFnPointer/ClosureFnPointer to a unique BV constant.
    ///
    /// Each distinct FnDef or Closure monomorphization gets a unique non-zero
    /// pointer value. This mirrors the CHC path's `translate_reify_fn_pointer`.
    /// The BMC path resolves actual fn-ptr calls at the terminator level via
    /// `try_codegen_fn_ptr_call`; this only ensures the assignment variable is
    /// constrained (preventing false CTREX from unconstrained locals).
    fn codegen_reify_fn_pointer(&mut self, operand: &Operand) -> Expr {
        let key = operand.ty(self.body.locals()).into_option().and_then(|ty| match ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, args)) => {
                Some(format!("{}_{:?}", def.trimmed_name(), args))
            }
            TyKind::RigidTy(RigidTy::Closure(def, args)) => {
                Some(format!("closure_{}_{:?}", def.trimmed_name(), args))
            }
            _ => None,
        });
        let id: u128 = match key {
            Some(ref k) => {
                use std::collections::hash_map::DefaultHasher;
                use std::hash::{Hash, Hasher};
                let mut hasher = DefaultHasher::new();
                k.hash(&mut hasher);
                let h = hasher.finish() as u128;
                (h & ((1u128 << POINTER_WIDTH) - 1)) | 1
            }
            None => 1,
        };
        Expr::bitvec_const(id, POINTER_WIDTH)
    }

    /// Handle ArrayToPointer, MutToConstPointer, and UnsafeFnPointer coercions.
    ///
    /// These are identity casts at the BV level in the pointer-based memory model:
    /// - ArrayToPointer: `&[T; N]` → `*const T` (same address, both BV64)
    /// - MutToConstPointer: `*mut T` → `*const T` (same address)
    /// - UnsafeFnPointer: `fn()` → `unsafe fn()` (same pointer)
    ///
    /// If both operand and target have the same sort, pass through.
    /// If the operand is Array sort (edge case where the array value leaks
    /// through instead of a pointer), fall back to `codegen_cast` which handles
    /// sort-pair dispatch.
    /// Part of #3192.
    fn codegen_array_to_pointer_cast(
        &mut self,
        operand: &Operand,
        target_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        let target_sort = Self::infer_sort_from_ty(target_ty)?;
        let expr = self.codegen_operand(operand)?;
        let src_sort = expr.sort().clone();
        // Common case: both are pointer-width BVs (identity cast).
        if src_sort == target_sort {
            return Some(expr);
        }
        // BV→BV width mismatch: delegate to codegen_cast for extension/truncation.
        if src_sort.is_bitvec() && target_sort.is_bitvec() {
            return self.codegen_cast(operand, target_ty);
        }
        // Array→BV edge case: the operand resolved to an actual array value
        // instead of a pointer. The target is a pointer (BV). In the pointer
        // model, we cannot extract a meaningful address from an SMT Array, so
        // we declare a fresh symbolic pointer. This is a sound over-approximation
        // (the pointer is unconstrained but valid as a nondeterministic address).
        if let SortInner::Array(_) = src_sort.inner() {
            if let SortInner::BitVec(_) = target_sort.inner() {
                warn!(
                    src_sort = ?src_sort,
                    target_sort = ?target_sort,
                    "ArrayToPointer: Array→BV sort mismatch, producing symbolic pointer"
                );
                let name = self.ctx.fresh_name("__array_to_ptr");
                return Some(self.ctx.declare_var(&name, target_sort));
            }
        }
        // Datatype→BV: single-field wrapper (e.g., fat pointer DT → thin pointer).
        // Fall through to codegen_cast for structural coercion.
        self.codegen_cast(operand, target_ty)
    }

    pub(super) fn codegen_cast(
        &mut self,
        operand: &Operand,
        target_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        let target_sort = Self::infer_sort_from_ty(target_ty)?;
        let src_ty = operand.ty(self.body.locals()).into_option();
        // Determine source signedness for extension/truncation direction.
        // Pointers and pointer-wrapper ADTs are treated as unsigned bitvectors for
        // cast purposes (Part of #2076), unlike ty_signedness which recurses through
        // them to find the inner type. This mirrors CHC ty_signedness_for_cast.
        // All other types delegate to recursive ty_signedness so arrays,
        // tuples, and repr-SIMD wrapper structs inherit payload signedness
        // instead of spuriously tripping cast fallback. Part of #2954.
        let src_signed = src_ty
            .and_then(|ty| match ty.kind() {
                // Part of #2076: Pointer types are unsigned for cast purposes.
                // Raw pointers and references are bitvec(POINTER_WIDTH) — treat as unsigned.
                TyKind::RigidTy(RigidTy::RawPtr(..)) | TyKind::RigidTy(RigidTy::Ref(..)) => {
                    Some(false)
                }
                // Pointer-wrapper ADTs (Box, Unique, NonNull) are unsigned pointers
                // for cast purposes — do NOT recurse into the inner type.
                // Without this, Box<i32> falls through to ty_signedness_shallow → None →
                // fallback, inflating the signedness_fallback counter with a spurious warning.
                TyKind::RigidTy(RigidTy::Adt(def, _))
                    if crate::codegen_ay::shared::is_pointer_wrapper_adt(&def.name()) =>
                {
                    Some(false)
                }
                _ => Self::ty_signedness(ty),
            })
            .unwrap_or_else(|| {
                crate::codegen_ay::shared::signedness_fallback_for_cast_or_coerce("codegen_cast")
            });
        let src_widen_signed =
            src_ty.as_ref().and_then(Self::single_field_adt_signedness).unwrap_or(src_signed);

        let enum_discriminants: Option<EnumDiscrInfo> = src_ty.as_ref().and_then(|ty| {
            if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind()
                && def.kind() == AdtKind::Enum
                && !def.variants().is_empty()
            {
                let internal_def = rustc_internal::internal(self.ctx.tcx, def);
                let first_discr = internal_def
                    .discriminant_for_variant(self.ctx.tcx, InternalVariantIdx::from_usize(0));
                let (repr_width, is_signed) = match rustc_internal::stable(first_discr.ty).kind() {
                    TyKind::RigidTy(RigidTy::Int(i)) => (int_ty_to_bitvec_width(i), true),
                    TyKind::RigidTy(RigidTy::Uint(u)) => (uint_ty_to_bitvec_width(u), false),
                    _ => (32, false), // external enum: TyKind — default repr for non-Int/Uint discriminants
                };
                let discrs: Vec<u128> = def
                    .variants()
                    .iter()
                    .enumerate()
                    .map(|(idx, _)| {
                        internal_def
                            .discriminant_for_variant(
                                self.ctx.tcx,
                                InternalVariantIdx::from_usize(idx),
                            )
                            .val
                    })
                    .collect();
                return Some(EnumDiscrInfo { values: discrs, repr_width, is_signed });
            }
            None
        });

        let expr = self.codegen_operand(operand)?;
        let src_sort = expr.sort().clone();

        match (src_sort.inner(), target_sort.inner()) {
            (SortInner::Bool, SortInner::Bool)
            | (SortInner::Int, SortInner::Int)
            | (SortInner::Real, SortInner::Real) => Some(expr),
            (SortInner::Datatype(s), SortInner::Datatype(t)) if s.name == t.name => Some(expr),
            (SortInner::Datatype(src_dt), SortInner::Datatype(tgt_dt)) => {
                let sign_ext = SignExtension::for_signedness(src_widen_signed);
                // Part of #3198: unified DT→DT structural coercion for both
                // single-field wrappers and multi-field types (e.g., Box<T>→Box<dyn Trait>).
                // Uses src_widen_signed from MIR type info for correct signedness.
                if let Some(result) = coerce_datatype_structural(
                    expr.clone(),
                    src_dt,
                    tgt_dt,
                    target_sort.clone(),
                    sign_ext,
                ) {
                    return Some(result);
                }
                // Part of #3192: aggressive DT→DT fallback handles field sort
                // pairs that coerce_datatype_structural cannot (Bool↔BV, Int↔BV,
                // Array identity). This eliminates UnconstrainedAssignment for
                // transmute-like casts between structurally compatible types.
                if let Some(result) =
                    coerce_dt_to_dt_fallback(expr, src_dt, tgt_dt, target_sort.clone(), sign_ext)
                {
                    return Some(result);
                }
                // Unsupported: DT→DT structural mismatch. Returning None lets
                // the caller handle this as an untranslatable cast rather than
                // silently producing an unconstrained variable (false-proof risk).
                // Part of #2423.
                warn!(
                    src = %src_dt.name, tgt = %tgt_dt.name,
                    "unsupported DT→DT cast: structural mismatch (not single-field wrapper)"
                );
                self.ctx.unsupported(
                    "Cast",
                    format!("DT→DT mismatch: {} → {}", src_dt.name, tgt_dt.name),
                );
                None
            }
            (SortInner::Bool, SortInner::BitVec(d)) => {
                let bv1 = Expr::ite(expr, Expr::bitvec_const(1, 1), Expr::bitvec_const(0, 1));
                if d.width == 1 { Some(bv1) } else { Some(bv1.zero_extend(d.width - 1)) }
            }
            (SortInner::BitVec(s), SortInner::Bool) => {
                Some(expr.ne(Expr::bitvec_const(0, s.width)))
            }
            (SortInner::BitVec(s), SortInner::BitVec(d)) => {
                if s.width == d.width {
                    Some(expr)
                } else if s.width < d.width {
                    Some(if src_signed {
                        expr.sign_extend(d.width - s.width)
                    } else {
                        expr.zero_extend(d.width - s.width)
                    })
                } else {
                    Some(expr.extract(d.width - 1, 0))
                }
            }
            (SortInner::Int, SortInner::BitVec(d)) => {
                // SMT-LIB int2bv uses modular semantics: result ≡ expr (mod 2^width).
                // This correctly handles negative Int values, unlike the previous
                // pattern (declare fresh bv + assert bv2int(bv)==expr) which used
                // unsigned bv2int and was UNSAT for negative inputs (#2403).
                Some(expr.int2bv(d.width))
            }
            (SortInner::BitVec(_), SortInner::Int) => {
                if src_signed {
                    Some(expr.bv2int_signed())
                } else {
                    Some(expr.bv2int())
                }
            }
            (SortInner::Int, SortInner::Real) => Some(expr.int_to_real()),
            (SortInner::Real, SortInner::Int) => {
                let name = self.ctx.fresh_name("real_to_int");
                let iv = self.ctx.declare_var(&name, int_sort());
                // Unconditional: these fresh solver-auxiliary variables must always
                // satisfy their floor constraints. The caller handles path conditions
                // via assert_ssa_def when assigning the result to a destination.
                self.ctx.assert(iv.clone().int_to_real().real_le(expr.clone()));
                self.ctx.assert(expr.real_lt(iv.clone().int_add(Expr::int_const(1)).int_to_real()));
                Some(iv)
            }
            (SortInner::Real, SortInner::BitVec(d)) => {
                // Compose Real→Int (floor) then Int→BV (modular).
                // Previously this declared an unconstrained fresh BV (#2404).
                let name = self.ctx.fresh_name("real_to_int_for_bv");
                let iv = self.ctx.declare_var(&name, int_sort());
                // Floor constraint: iv <= expr < iv + 1
                self.ctx.assert(iv.clone().int_to_real().real_le(expr.clone()));
                self.ctx.assert(expr.real_lt(iv.clone().int_add(Expr::int_const(1)).int_to_real()));
                Some(iv.int2bv(d.width))
            }
            (SortInner::BitVec(_), SortInner::Real) => {
                Some((if src_signed { expr.bv2int_signed() } else { expr.bv2int() }).int_to_real())
            }
            (SortInner::Datatype(dt), SortInner::BitVec(d)) => self.codegen_dt_to_bv(
                &expr,
                operand,
                dt,
                d.width,
                enum_discriminants,
                src_widen_signed,
            ),
            (SortInner::BitVec(s), SortInner::Datatype(d)) => {
                // Part of #3198: BV→Dyn fat pointer construction via shared helper.
                // When target is a Dyn_Trait sort, construct {fld_ptr: source, fld_vtable: 0}.
                // BMC sort-level fallback uses dummy vtable=0; CHC path uses real vtable IDs.
                if let Some(ptr_w) = d
                    .constructors
                    .first()
                    .and_then(|c| c.fields.first())
                    .and_then(|f| f.sort.bitvec_width())
                {
                    let vtable_dummy = Expr::bitvec_const(0u64, ptr_w);
                    if let Some(result) = construct_dyn_fat_pointer(
                        expr.clone(),
                        d,
                        target_sort.clone(),
                        vtable_dummy,
                    ) {
                        return Some(result);
                    }
                }
                // Part of #3041 Mode 5: BV→DT cast for niche-optimized Option-like enums.
                // Rust's niche optimization stores Option<NonZero*> as the raw integer
                // (0 = None, nonzero = Some(value)). The MIR generates transmute-like
                // casts between the integer representation and the Option Datatype.
                // Encode as: ite(bv == 0, None_ctor, Some_ctor(bv)).
                if d.constructors.len() == 2 {
                    let (none_idx, some_idx) = if d.constructors[0].fields.is_empty()
                        && d.constructors[1].fields.len() == 1
                    {
                        (0, 1)
                    } else if d.constructors[1].fields.is_empty()
                        && d.constructors[0].fields.len() == 1
                    {
                        (1, 0)
                    } else {
                        (usize::MAX, usize::MAX) // sentinel: not Option-like
                    };
                    if none_idx != usize::MAX
                        && let Some(payload_field) = d.constructors[some_idx].fields.first()
                        && let Some(payload_w) = payload_field.sort.bitvec_width()
                        && payload_w == s.width
                    {
                        let none_ctor = &d.constructors[none_idx];
                        let some_ctor = &d.constructors[some_idx];
                        let niche = Expr::bitvec_const(0u64, s.width);
                        let is_none = expr.clone().eq(niche);
                        let none_val = Expr::datatype_constructor(
                            &d.name,
                            &none_ctor.name,
                            vec![],
                            target_sort.clone(),
                        );
                        let some_val = Expr::datatype_constructor(
                            &d.name,
                            &some_ctor.name,
                            vec![expr],
                            target_sort.clone(),
                        );
                        return Some(Expr::ite(is_none, none_val, some_val));
                    }
                }
                // Single-constructor struct wrapping: BV → Struct(bv_field).
                // Handles newtype wrappers like NonZeroU128 where the DT is a
                // single-constructor, single-field struct with matching BV width.
                if d.constructors.len() == 1
                    && let Some(cons) = d.constructors.first()
                    && cons.fields.len() == 1
                    && let Some(field) = cons.fields.first()
                    && let Some(field_w) = field.sort.bitvec_width()
                    && field_w == s.width
                {
                    return Some(Expr::datatype_constructor(
                        &d.name,
                        &cons.name,
                        vec![expr],
                        target_sort.clone(),
                    ));
                }
                // Unsupported: BV→DT cast. Returning None lets the caller
                // handle this as an untranslatable cast rather than silently
                // producing an unconstrained variable (false-proof risk).
                // Part of #2423.
                warn!(
                    src_width = s.width, tgt = %d.name,
                    "unsupported BV→DT cast: no encoding for integer-to-datatype"
                );
                self.ctx.unsupported("Cast", format!("BV→DT: bv{} → {}", s.width, d.name));
                None
            }
            // Part of #3806: DT→Array for SIMD transmute (e.g., i64x2 → [i64; 2]).
            // SIMD types are single-field struct wrappers around arrays. When
            // transmute produces a Cast(Transmute, Simd → [T; N]), extract the
            // inner array field from the Datatype constructor.
            (SortInner::Datatype(dt), SortInner::Array(tgt_arr))
                if dt.constructors.len() == 1
                    && dt.constructors[0].fields.len() == 1
                    && dt.constructors[0].fields[0].sort.array_sort().is_some_and(|arr| {
                        arr.index_sort == tgt_arr.index_sort
                            && arr.element_sort == tgt_arr.element_sort
                    }) =>
            {
                let f = &dt.constructors[0].fields[0];
                Some(expr.field_select(&*dt.name, &*f.name, f.sort.clone()))
            }
            // Part of #3806: Array→Array identity for same-sort transmute.
            (SortInner::Array(s), SortInner::Array(t))
                if s.index_sort == t.index_sort && s.element_sort == t.element_sort =>
            {
                Some(expr)
            }
            // Remaining sort-pair casts: not yet supported.
            // Array casts, Datatype↔Int/Real/Bool, and Bool↔Int/Real
            // are not produced by standard Rust MIR casts.
            (SortInner::Bool, SortInner::Int)
            | (SortInner::Bool, SortInner::Real)
            | (SortInner::Bool, SortInner::Datatype(_))
            | (SortInner::Bool, SortInner::Array(_))
            | (SortInner::Int, SortInner::Bool)
            | (SortInner::Int, SortInner::Datatype(_))
            | (SortInner::Int, SortInner::Array(_))
            | (SortInner::Real, SortInner::Bool)
            | (SortInner::Real, SortInner::Datatype(_))
            | (SortInner::Real, SortInner::Array(_))
            | (SortInner::BitVec(_), SortInner::Array(_))
            | (SortInner::Datatype(_), SortInner::Bool)
            | (SortInner::Datatype(_), SortInner::Int)
            | (SortInner::Datatype(_), SortInner::Real)
            | (SortInner::Datatype(_), SortInner::Array(_))
            | (SortInner::Array(_), _)
            | (SortInner::String, _)
            | (_, SortInner::String)
            | (SortInner::FloatingPoint(_, _), _)
            | (_, SortInner::FloatingPoint(_, _))
            | (SortInner::Uninterpreted(_), _)
            | (_, SortInner::Uninterpreted(_))
            | (SortInner::RegLan, _)
            | (_, SortInner::RegLan) => {
                self.ctx.unsupported("Cast", format!("{:?}", operand));
                None
            }
            (_, _) => {
                self.ctx.unsupported("Cast", format!("{:?}", operand));
                None
            }
        }
    }
}
