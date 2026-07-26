// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Core type-to-sort translation for CHC codegen.
//!
//! Pure type-to-sort mapping with no state mutation — all functions are
//! associated functions on `ChcCtx` via extension trait.
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.

use ay_bindings::Sort;
use rustc_middle::ty::tls;
use rustc_public::CrateDef;
use rustc_public::ty::{AdtDef, GenericArgKind, GenericArgs, RigidTy, TyKind};
use std::fmt::Write as _;
use tracing::{debug, warn};

use crate::codegen_ay::coroutine_layout::build_coroutine_sort_info;
use crate::codegen_ay::type_depth_guard::TypeDepthGuard;
use crate::codegen_ay::types::{
    POINTER_WIDTH, bool_sort, bv8_sort, flatten_dt_array_element, float_ty_to_bitvec_width,
    int_ty_to_bitvec_width, ptr_sort, uint_ty_to_bitvec_width,
};
use crate::rustc_public_bridge::IndexedVal;

use super::ChcCtx;
use super::codegen_types_adt::CodegenTypesAdt;
use super::codegen_types_adt_sort::CodegenTypesAdtSort;
use super::names::{self, struct_sort};

/// Extension trait for core type-to-sort translation on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CodegenTypes<'tcx, 'body> {
    fn deref_ref_ty(ty: rustc_public::ty::Ty) -> (rustc_public::ty::Ty, bool);
    fn ref_pointee_is_fat_bv128(pointee: rustc_public::ty::Ty) -> bool;
    fn deref_ref_ty_sized_only(ty: rustc_public::ty::Ty) -> (rustc_public::ty::Ty, bool);
    fn option_sort_name_for_payload(payload_ty: rustc_public::ty::Ty) -> String;
    fn option_like_sort_name(
        def: AdtDef,
        args: &GenericArgs,
        payload_ty: rustc_public::ty::Ty,
    ) -> String;
    #[must_use]
    fn translate_ty(ty: rustc_public::ty::Ty) -> Option<Sort>;
}

impl<'tcx, 'body> CodegenTypes<'tcx, 'body> for ChcCtx<'tcx, 'body> {
    fn deref_ref_ty(ty: rustc_public::ty::Ty) -> (rustc_public::ty::Ty, bool) {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => (inner, true),
            // RawPtr: (inner_type, mutability) per sort_inference.rs:61
            TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => (inner, true),
            _ => (ty, false), // external enum: TyKind
        }
    }

    /// Returns true when `&pointee` / `*pointee` is encoded as a BV128 fat
    /// pointer (`concat(len: BV64, data_ptr: BV64)`) by `translate_ty`:
    /// `str`, slices, and ADTs with unsized slice tails (custom DSTs).
    ///
    /// Mirrors the Ref/RawPtr fat-pointer match in `translate_ty` (#134/#4163).
    /// Note: `dyn Trait` pointees are NOT in this set — they are modeled by
    /// value as the `Dyn_Trait{fld_ptr, fld_vtable}` datatype after deref.
    fn ref_pointee_is_fat_bv128(pointee: rustc_public::ty::Ty) -> bool {
        match pointee.kind() {
            TyKind::RigidTy(RigidTy::Slice(_) | RigidTy::Str) => true,
            TyKind::RigidTy(RigidTy::Adt(..)) => {
                use crate::kani_middle::abi::LayoutOf;
                LayoutOf::new(pointee).has_slice_tail()
            }
            _ => false,
        }
    }

    /// Like `deref_ref_ty`, but only strips references to *sized* pointees
    /// (which are deliberately modeled by value). References to unsized
    /// fat-pointer pointees (`&str`, `&[T]`, slice-tail DSTs) are kept intact
    /// so the declared sort matches the BV128 fat-pointer value representation
    /// (`translate_ty(&str) == BV128`). Without this gate, `Option<&str>`
    /// payload fields were declared as `Array(BV64, BV8)` (via bare `str`)
    /// while values flowed as BV128 fat pointers, producing ill-sorted
    /// datatype constructor applications that fail AY's parser.
    fn deref_ref_ty_sized_only(ty: rustc_public::ty::Ty) -> (rustc_public::ty::Ty, bool) {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _))
                if Self::ref_pointee_is_fat_bv128(inner) =>
            {
                (ty, false)
            }
            _ => Self::deref_ref_ty(ty),
        }
    }

    fn option_sort_name_for_payload(payload_ty: rustc_public::ty::Ty) -> String {
        let mut payload_ty_name = String::with_capacity(32);
        let _ = write!(&mut payload_ty_name, "{payload_ty}");
        names::option_sort_name(&names::sanitize_adt_suffix(&payload_ty_name))
    }

    fn option_like_sort_name(
        def: AdtDef,
        args: &GenericArgs,
        payload_ty: rustc_public::ty::Ty,
    ) -> String {
        if def.trimmed_name() == "Option" {
            Self::option_sort_name_for_payload(payload_ty)
        } else {
            Self::adt_sort_name(def, args)
        }
    }

    /// Translates a Rust type to a AY sort.
    ///
    /// Returns None for types that cannot be directly represented in SMT.
    /// Protected by `TypeDepthGuard` to prevent stack overflow on deeply
    /// nested or self-referential types.
    fn translate_ty(ty: rustc_public::ty::Ty) -> Option<Sort> {
        let _depth_guard = TypeDepthGuard::acquire()?;
        debug!(?ty, "translate_ty called");
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Bool) => Some(bool_sort()),
            TyKind::RigidTy(RigidTy::Int(k)) => Some(Sort::bitvec(int_ty_to_bitvec_width(k))),
            TyKind::RigidTy(RigidTy::Uint(k)) => Some(Sort::bitvec(uint_ty_to_bitvec_width(k))),
            TyKind::RigidTy(RigidTy::Float(k)) => {
                // Part of #3447: track FP-as-BV encoding as sound over-approximation.
                //
                // AUDIT (task #65, fp_bitvector_encoding): this increments per
                // float SORT DECLARATION (38x on FastMath/add_f32), NOT per
                // lossily-encoded float OPERATION, so it must never reach the
                // driver's DEMOTED table raw — it would demote clean float
                // proofs that are sound by construction under the congruent
                // float-binop table + NaN-check obligation. Relocation to
                // operation-level sites found NO current CHC target: symbolic
                // f32/f64 binops go through the congruent table (sound,
                // fail-closed by the NaN check), f16/f128 binops fail closed
                // via the demoting chc_fallback, and float-cast fallbacks are
                // tracked via record_sound_fallback_reason. The counter is
                // therefore left un-plumbed on the generate_metadata
                // (codegen_units.rs) path — see the comment there — and kept
                // here only for the codegen_results writer path, whose float
                // lanes need their own audit before this can be removed
                // (removing it un-demotes that path's float harnesses).
                crate::codegen_ay::chc::codegen_ctx::globals::record_fp_bitvector_encoding();
                Some(Sort::bitvec(float_ty_to_bitvec_width(k)))
            }
            TyKind::RigidTy(RigidTy::Char) => Some(Sort::bitvec(32)),
            // Part of #134: fat raw pointers to slices/str carry metadata (length).
            // Encode as BV128 = concat(len:BV64, data:BV64) so comparison code
            // in raw_pointer_components can decompose via extract(63,0) / extract(127,64).
            // Thin pointers (Sized pointees) remain BV64.
            // Part of #4163: ADTs with unsized slice/str tails (custom DSTs like
            // `MyStr { header: u8, data: str }`) are also fat pointers.
            TyKind::RigidTy(RigidTy::RawPtr(pointee, _) | RigidTy::Ref(_, pointee, _)) => {
                match pointee.kind() {
                    TyKind::RigidTy(RigidTy::Slice(_) | RigidTy::Str) => {
                        Some(Sort::bitvec(2 * POINTER_WIDTH))
                    }
                    TyKind::RigidTy(RigidTy::Adt(..)) => {
                        use crate::kani_middle::abi::LayoutOf;
                        if LayoutOf::new(pointee).has_slice_tail() {
                            Some(Sort::bitvec(2 * POINTER_WIDTH))
                        } else {
                            Some(ptr_sort())
                        }
                    }
                    _ => Some(ptr_sort()),
                }
            }
            // Function values (FnDef/FnPtr) are pointer-sized operands in MIR.
            TyKind::RigidTy(RigidTy::FnDef(_, _) | RigidTy::FnPtr(_)) => Some(ptr_sort()),
            // Part of #3159: dyn Trait objects are fat pointers (ptr + vtable).
            // Encode as Dyn_Trait{fld_ptr: BV64, fld_vtable: BV64} datatype.
            // collect_state_vars will auto-flatten this to 2 scalar BV64 state vars
            // via the recursive flattening logic (#2989), keeping relation arity
            // PDR-friendly while preserving vtable discriminant information.
            TyKind::RigidTy(RigidTy::Dynamic(..)) => {
                let name = names::dyn_sort_name("Trait");
                Some(struct_sort(name, [("fld_ptr", ptr_sort()), ("fld_vtable", ptr_sort())]))
            }
            // #1166: Never type (!) - uninhabited, model as Bool.
            TyKind::RigidTy(RigidTy::Never) => {
                debug!("Never type -> Bool (unreachable)");
                Some(bool_sort())
            }
            TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.is_empty() => {
                // Unit type
                Some(bool_sort())
            }
            // Non-empty tuples: encode as SMT struct (Part of #647)
            TyKind::RigidTy(RigidTy::Tuple(tys)) => {
                let fields: Vec<(std::borrow::Cow<'static, str>, Sort)> = tys
                    .iter()
                    .enumerate()
                    .filter_map(|(i, elem_ty)| {
                        let elem_sort = Self::translate_ty(*elem_ty)?;
                        Some((names::tuple_field_name(i), elem_sort))
                    })
                    .collect();
                if fields.len() == tys.len() {
                    // #1979: Single-element tuples unwrap to their element.
                    if let [(_, sole_sort)] = &fields[..] {
                        return Some(sole_sort.clone());
                    }
                    let tuple_name = Self::tuple_sort_name(&fields);
                    Some(struct_sort(tuple_name, fields))
                } else {
                    None
                }
            }
            // Arrays: encode as SMT array with BitVec index (Part of #647, #652)
            // Part of #1739: Flatten Datatype elements to BV for PDR compatibility.
            // Z3 PDR treats Datatype accessors as uninterpreted when applied to
            // Array-stored Datatypes ("Uninterpreted 'value' in <null>"), causing
            // UNKNOWN. BV elements + coercion at boundaries avoids this.
            //
            // ZST element arrays ([(); N]) have exactly one inhabitant per element
            // and carry zero bits. Encode as Bool to match the ZST pipeline
            // (kani::any, canonical_zst_expr, coerce_store_value). Without this,
            // Array(BV64, Bool) sorts in ADT fields cause coerce_store_value to
            // substitute fresh symbolics and lose data.
            // Note: [T; 0] is NOT folded to Bool — the code may use array
            // operations (clone, eq) that expect the Array sort.
            TyKind::RigidTy(RigidTy::Array(elem_ty, _len)) => {
                let is_zst_elem = matches!(
                    elem_ty.kind(),
                    TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.is_empty()
                ) || matches!(elem_ty.kind(), TyKind::RigidTy(RigidTy::Never));
                if is_zst_elem {
                    return Some(bool_sort());
                }
                let elem_sort = Self::translate_ty(elem_ty)?;
                let elem_sort = flatten_dt_array_element(elem_sort);
                Some(Sort::array(ptr_sort(), elem_sort))
            }
            // Slices: same as arrays with BitVec index (#652)
            // Part of #1739: same DT→BV flattening as arrays.
            TyKind::RigidTy(RigidTy::Slice(elem_ty)) => {
                let elem_sort = Self::translate_ty(elem_ty)?;
                let elem_sort = flatten_dt_array_element(elem_sort);
                Some(Sort::array(ptr_sort(), elem_sort))
            }
            // ADT types: delegate to codegen_types_adt.rs
            TyKind::RigidTy(RigidTy::Adt(def, args)) => Self::translate_adt_ty(def, args),
            // #2083: Closure types — map to SMT datatype matching codegen_closure_aggregate.
            TyKind::RigidTy(RigidTy::Closure(def, args)) => {
                let closure_id = def.0.to_index();
                let closure_name = crate::codegen_ay::names::closure_sort_name(closure_id);

                // Prefer canonical closure-generic decoding (FnPtr + tupled_upvars).
                // Fall back to the trailing tuple type because rustc can prepend
                // additional generic arguments in some closure contexts.
                let upvar_tys: Vec<rustc_public::ty::Ty> = args
                    .0
                    .iter()
                    .enumerate()
                    .find_map(|(pos, arg)| {
                        if matches!(arg, GenericArgKind::Type(ty) if matches!(ty.kind(), TyKind::RigidTy(RigidTy::FnPtr(_))))
                        {
                            match args.0.get(pos + 1) {
                                Some(GenericArgKind::Type(ty)) => match ty.kind() {
                                    TyKind::RigidTy(RigidTy::Tuple(tys)) => Some(tys),
                                    _ => None, // external enum: TyKind
                                },
                                _ => None, // external enum: GenericArgKind
                            }
                        } else {
                            None
                        }
                    })
                    .or_else(|| {
                        args.0.iter().rev().find_map(|arg| match arg {
                            GenericArgKind::Type(ty) => match ty.kind() {
                                TyKind::RigidTy(RigidTy::Tuple(tys)) => Some(tys),
                                _ => None, // external enum: TyKind
                            },
                            _ => None, // external enum: GenericArgKind
                        })
                    })
                    .unwrap_or_default();

                if upvar_tys.is_empty() {
                    // Part of #2244: Non-capturing closures are ZSTs. Use Bool
                    // instead of empty Datatype to avoid Datatype sorts in CHC
                    // relation signatures (PDR can't synthesize invariants
                    // with Datatype parameters).
                    debug!(closure_name, "non-capturing closure -> Bool (ZST)");
                    Some(bool_sort())
                } else {
                    let fields: Vec<_> = upvar_tys
                        .iter()
                        .enumerate()
                        .map(|(i, upvar_ty)| {
                            let sort = Self::translate_ty(*upvar_ty).unwrap_or_else(|| {
                                // Avoid bubbling `None` to local state-var declaration,
                                // which degrades the whole closure local to an opaque bv32.
                                warn!(
                                    closure_name = %closure_name,
                                    capture_index = i,
                                    ?upvar_ty,
                                    "closure upvar sort fallback to pointer-width bitvec"
                                );
                                ptr_sort()
                            });
                            // Part of #2267: Cow<str> implements Into<String> for struct_sort.
                            (crate::codegen_ay::names::capture_field_name(i), sort)
                        })
                        .collect();

                    debug!(closure_name, num_captures = fields.len(), "closure -> Datatype sort");
                    Some(struct_sort(closure_name, fields))
                }
            }
            // Part of #1351: Coroutine types — explicit root state machine with nested views.
            TyKind::RigidTy(RigidTy::Coroutine(def, args)) => tls::with(|tcx| {
                let coroutine_ty =
                    rustc_public::ty::Ty::from_rigid_kind(RigidTy::Coroutine(def, args.clone()));
                let info = build_coroutine_sort_info(tcx, coroutine_ty, |field_ty| {
                    Self::translate_ty(field_ty).unwrap_or_else(|| {
                        warn!(?field_ty, "coroutine field sort fallback to pointer-width bitvec");
                        ptr_sort()
                    })
                })?;

                debug!(
                    direct_fields = info.direct_fields.fields.len(),
                    variants = info.variants.len(),
                    "coroutine -> Datatype sort"
                );
                Some(info.root_sort)
            }),
            // Part of #3159: Foreign types (extern type) like std::ptr::metadata::VTable.
            // These are opaque unsized types that only appear behind pointers; encode
            // as pointer-width bitvec for consistency with pointer arithmetic.
            TyKind::RigidTy(RigidTy::Foreign(_)) => Some(ptr_sort()),
            // Phase 1: Bare `str` type (not behind a pointer). Encode as Array(BV64, BV8)
            // consistent with Slice(u8) and the BMC encoder's slice_sort(bv8_sort()).
            // Part of #4251: eliminates bv32 fallback for string-method internals.
            TyKind::RigidTy(RigidTy::Str) => {
                debug!("Str type -> Array(ptr, bv8)");
                Some(Sort::array(ptr_sort(), bv8_sort()))
            }
            // Phase 1: Pattern types (RFC 3627) wrap a base type with niche restrictions.
            // The niche constraint doesn't affect sort representation — delegate to base.
            // Part of #4251.
            TyKind::RigidTy(RigidTy::Pat(base_ty, ..)) => {
                debug!(?base_ty, "Pat type -> delegate to base");
                Self::translate_ty(base_ty)
            }
            // Phase 2: Async closures — unsupported in upstream Kani (kani#3783).
            // Return None so callers apply their existing fallback path.
            // Part of #4251.
            TyKind::RigidTy(RigidTy::CoroutineClosure(_, _)) => {
                warn!(?ty, "CoroutineClosure unsupported (kani#3783)");
                None
            }
            // Phase 2: Coroutine witness types — used by borrow-checker only, should
            // not appear in codegen (Kani treats as unreachable). Defensive arm.
            // Part of #4251.
            TyKind::RigidTy(RigidTy::CoroutineWitness(_, _)) => {
                debug!(?ty, "CoroutineWitness in translate_ty — should be unreachable");
                None
            }
            // Phase 1: Unresolved generic parameter. Should not appear post-monomorphization
            // but leaks through in some std MIR trait method bodies. Use ptr_sort() as safe
            // over-approximation, consistent with translate_type_arg_sort_or_param_bv.
            // Part of #4251.
            TyKind::Param(param_ty) => {
                warn!(?param_ty, "TyKind::Param in translate_ty — expected monomorphized type");
                Some(ptr_sort())
            }
            // Phase 2: Type alias / associated type projection. Should be normalized by
            // rustc before reaching codegen (Kani treats as unreachable). Use ptr_sort()
            // as safe over-approximation when normalization leaks through.
            // Part of #4251.
            TyKind::Alias(..) => {
                warn!(?ty, "TyKind::Alias in translate_ty — expected normalized type");
                Some(ptr_sort())
            }
            _ => {
                // external enum: TyKind
                debug!(?ty, "unmatched type in translate_ty");
                None
            }
        }
    }
}
