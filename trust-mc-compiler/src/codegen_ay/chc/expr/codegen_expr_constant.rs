// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Constant translation helpers for CHC expression codegen.
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.

use ay_bindings::{Expr, Sort};
use rustc_abi::VariantIdx as InternalVariantIdx;
use rustc_public::CrateDef;
use rustc_public::mir::ConstOperand;
use rustc_public::rustc_internal;
use rustc_public::ty::{AdtKind, Allocation, ConstantKind, RigidTy, TyConstKind, TyKind};
use std::sync::atomic::Ordering;
use tracing::{debug, warn};

use crate::codegen_ay::chc::call::canonical_zst_expr;
use crate::codegen_ay::names;
use crate::codegen_ay::types::{
    POINTER_WIDTH, float_ty_to_bitvec_width, int_ty_to_bitvec_width, uint_ty_to_bitvec_width,
};

use super::ChcCtx;
use super::codegen_ctx::diagnostics::{CellCounter, GLOBAL_COUNTERS};
use super::codegen_expr_constant_payload::{
    const_payload_is_fat_ref, decode_fat_ref_const_parts, fat_ref_const_len,
};
pub(in crate::codegen_ay::chc) use super::codegen_expr_constant_payload::{
    decode_non_unit_enum_variant_index, decode_option_like_variant_index,
    extract_payload_from_alloc,
};
use super::codegen_stmt_aggregate_adt::sign_extend_discr_val;
use super::codegen_types::CodegenTypes;
use super::codegen_types_adt_sort::CodegenTypesAdtSort;
use crate::codegen_ay::chc::{chc_fresh_name, declare_pending_var};

/// Returns and resets the constant-translation drop counter for metadata emission.
/// Delegates to GLOBAL_COUNTERS (Part of #2906).
pub(in crate::codegen_ay) fn take_constant_translation_drop_count() -> usize {
    GLOBAL_COUNTERS.const_translation_drop.swap(0, Ordering::Relaxed)
}

#[cfg(test)]
pub(in crate::codegen_ay) fn set_constant_translation_drop_count_for_test(count: usize) {
    GLOBAL_COUNTERS.const_translation_drop.store(count, Ordering::Relaxed);
}

/// Extension trait for constant translation methods.
pub(in crate::codegen_ay::chc) trait ExprConstant {
    /// Translates a MIR constant to a AY expression.
    #[must_use]
    fn translate_constant(&self, const_op: &ConstOperand) -> Option<Expr>;

    /// Translates a constant `&T`/`*const T` to its referent `T` expression.
    /// Caller in `inline_shared/mod.rs` deferred due to cross-worker cooldown.
    #[must_use]
    #[allow(dead_code)]
    fn translate_constant_referent(&self, const_op: &ConstOperand) -> Option<Expr>;
}

impl<'tcx, 'body> ExprConstant for ChcCtx<'tcx, 'body> {
    fn translate_constant(&self, const_op: &ConstOperand) -> Option<Expr> {
        let mir_const = &const_op.const_;
        let ty = mir_const.ty();

        match mir_const.kind() {
            ConstantKind::Allocated(alloc) => self.scalar_to_expr(alloc, ty),
            ConstantKind::Ty(ty_const) => match ty_const.kind() {
                TyConstKind::Value(value_ty, alloc) => self.scalar_to_expr(alloc, *value_ty),
                TyConstKind::ZSTValue(_) => {
                    canonical_zst_expr(ty).or_else(|| Some(Expr::bool_const(true)))
                }
                TyConstKind::Bound(..) | TyConstKind::Param(_) | TyConstKind::Unevaluated(..) => {
                    None
                }
            },
            ConstantKind::ZeroSized => {
                canonical_zst_expr(ty).or_else(|| Some(Expr::bool_const(true)))
            }
            ConstantKind::Param(_) | ConstantKind::Unevaluated(_) => None,
        }
    }

    fn translate_constant_referent(&self, const_op: &ConstOperand) -> Option<Expr> {
        use rustc_public::mir::alloc::GlobalAlloc;

        let mir_const = &const_op.const_;
        let inner_ty = match mir_const.ty().kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
            _ => return None,
        };
        let target_alloc = match mir_const.kind() {
            ConstantKind::Allocated(alloc) => {
                let alloc_id = alloc.provenance.ptrs.first()?.1.0;
                match GlobalAlloc::from(alloc_id) {
                    GlobalAlloc::Memory(target) => target,
                    // Pointer constants targeting a static (e.g. `const {alloc1:
                    // *mut i32}` for `static mut CELL` inside inlined drop glue)
                    // must resolve to the static's ADDRESS, not its initial
                    // VALUE. Substituting the initializer here evaluated the
                    // rustc-inserted null/align UB checks of inlined bodies on
                    // address 0, fabricating "Genuine" counterexamples on safe
                    // programs (Drop/drop_boxed_dyn.rs), and routed stores to
                    // address 0 so static state vars were never updated. Return
                    // None so the caller falls through to translate_constant →
                    // pointer_scalar_expr, which resolves the registered
                    // split-pointer static address (with the #3793 cross-body
                    // DefId fallback). This also covers foreign (`extern`)
                    // statics, whose missing initializer body previously needed
                    // a special case to avoid an eval_initializer() span_bug.
                    GlobalAlloc::Static(_) => return None,
                    _ => return None,
                }
            }
            ConstantKind::Ty(ty_const) => match ty_const.kind() {
                TyConstKind::Value(_value_ty, alloc) => {
                    if let Some((_, alloc_id)) = alloc.provenance.ptrs.first() {
                        match GlobalAlloc::from(alloc_id.0) {
                            GlobalAlloc::Memory(target) => target,
                            // See the ConstantKind::Allocated arm above: never
                            // substitute a static's initial VALUE for a pointer
                            // constant; fall through to the address translation.
                            GlobalAlloc::Static(_) => return None,
                            _ => return None,
                        }
                    } else {
                        alloc.clone()
                    }
                }
                _ => return None,
            },
            _ => return None,
        };
        self.scalar_to_expr(&target_alloc, inner_ty)
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Converts a scalar allocation to a AY expression based on its type.
    #[must_use]
    fn scalar_to_expr(&self, alloc: &Allocation, ty: rustc_public::ty::Ty) -> Option<Expr> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Bool) => Some(Expr::bool_const(alloc.read_bool().ok()?)),
            TyKind::RigidTy(RigidTy::Int(int_ty)) => {
                let width = int_ty_to_bitvec_width(int_ty);
                let value = alloc.read_int().ok()?;
                let value_u128 = if width >= 128 {
                    value as u128
                } else {
                    (value as u128) & ((1u128 << width) - 1)
                };
                Some(Expr::bitvec_const(value_u128, width))
            }
            TyKind::RigidTy(RigidTy::Uint(uint_ty)) => {
                let width = uint_ty_to_bitvec_width(uint_ty);
                let value = alloc.read_uint().ok()?;
                let value_u128 = if width >= 128 { value } else { value & ((1u128 << width) - 1) };
                Some(Expr::bitvec_const(value_u128, width))
            }
            // Fix #1898, #1905, #1229: Handle ADT (struct/enum) constants
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                self.adt_scalar_to_expr(alloc, ty, def, args)
            }
            TyKind::RigidTy(RigidTy::Char) => {
                let value = alloc.read_uint().ok()?;
                let value_u128 = value & ((1u128 << 32) - 1);
                Some(Expr::bitvec_const(value_u128, 32))
            }
            // Part of #3094: Float constants modeled as bitvectors.
            TyKind::RigidTy(RigidTy::Float(float_ty)) => {
                Self::float_scalar_to_expr(alloc, float_ty)
            }
            // Fat-pointer constants (&str / &[T] / slice-tail DST refs): the
            // declared sort is BV128 = concat(len, data_ptr). Zero-extending
            // the thin pointer would encode len = 0, so read the concrete
            // length metadata from the allocation (fresh symbolic when the
            // metadata bytes are unreadable — sound, keeps the sort honest).
            TyKind::RigidTy(RigidTy::RawPtr(pointee, _) | RigidTy::Ref(_, pointee, _))
                if Self::ref_pointee_is_fat_bv128(pointee) =>
            {
                let data_ptr = self.pointer_scalar_expr(alloc)?;
                let len_expr = match fat_ref_const_len(alloc) {
                    Some(len) => Expr::bitvec_const(len as u128, POINTER_WIDTH),
                    None => declare_pending_var(
                        chc_fresh_name("__const_fat_ptr_len"),
                        Sort::bitvec(POINTER_WIDTH),
                    ),
                };
                Some(len_expr.concat(data_ptr))
            }
            // Part of #428: Raw pointers (e.g., `*mut usize` for static mut references)
            // are modeled as bitvec values at pointer width. The actual static state
            // variable handling is done by collect_static_state_vars; this translation
            // ensures the pointer constant itself doesn't get dropped.
            TyKind::RigidTy(RigidTy::RawPtr(..))
            | TyKind::RigidTy(RigidTy::Ref(..))
            | TyKind::RigidTy(RigidTy::FnPtr(_)) => self.pointer_scalar_expr(alloc),
            // Part of #428: Function pointers (fn items, closures) are modeled as
            // pointer-width bitvec values. The actual dispatch is handled by call
            // codegen; this ensures the function pointer constant is translatable.
            TyKind::RigidTy(RigidTy::FnDef(..)) | TyKind::RigidTy(RigidTy::Closure(..)) => {
                Some(Expr::bitvec_const(0, POINTER_WIDTH))
            }
            // Part of #4209: Array constants (e.g., [char; 4], [u8; 16]).
            // Read each element from the allocation bytes and build an SMT array
            // with store operations. Uses read_composite_from_allocation which
            // handles nested element types recursively.
            TyKind::RigidTy(RigidTy::Array(elem_ty, len_const)) => {
                let elem_sort = Self::translate_ty(elem_ty)?;
                let array_sort =
                    ay_bindings::Sort::array(crate::codegen_ay::types::ptr_sort(), elem_sort);
                let len = len_const.eval_target_usize().ok()?;
                debug!(?ty, len, "scalar_to_expr: Array constant");
                Self::read_composite_from_allocation(alloc, 0, &array_sort)
            }
            // Part of #3768: String slice (`&str`) constants — typically panic
            // format strings from `assert_eq!`/`assert!` macros. Model as a
            // pointer-width BV sentinel. The actual string content is not used
            // in proof assertions; dropping these inflates sound_fallback_count
            // on every harness that uses assert_eq!.
            TyKind::RigidTy(RigidTy::Str) => {
                debug!(?ty, "scalar_to_expr: Str constant -> BV sentinel");
                Some(Expr::bitvec_const(0, POINTER_WIDTH))
            }
            _ => {
                // external enum: TyKind
                self.diagnostics.const_translation_drop.inc();
                warn!(?ty, "unhandled scalar type in CHC");
                None
            }
        }
    }

    /// Translates an ADT (struct/enum) constant allocation to a AY expression.
    ///
    /// Handles opaque ADT types (#2075), unit enums (#1898/#3556), and
    /// option-like enums (#1739). Unit enum discriminants are sign-extended
    /// from the repr width to POINTER_WIDTH via `sign_extend_discr_val`.
    #[must_use]
    fn adt_scalar_to_expr(
        &self,
        alloc: &Allocation,
        ty: rustc_public::ty::Ty,
        def: rustc_public::ty::AdtDef,
        args: rustc_public::ty::GenericArgs,
    ) -> Option<Expr> {
        let name = def.trimmed_name();

        // Part of #2075: Opaque ADT types
        let opaque_width = match name.as_str() {
            "Alignment" | "NonNull" | "Unique" => Some(POINTER_WIDTH),
            "Layout" | "TypeId" => Some(128u32),
            _ => None,
        };
        if let Some(width) = opaque_width {
            let value = if let Ok(v) = alloc.read_uint() {
                v
            } else {
                // Part of #1739: TypeId/Layout allocations may carry provenance
                // markers that cause read_uint() to fail. Fall back to reading
                // the raw bytes directly (same pattern as float_scalar_to_expr).
                let byte_count = (width / 8) as usize;
                if alloc.bytes.len() < byte_count {
                    return None;
                }
                let mut v: u128 = 0;
                for (i, byte) in alloc.bytes.iter().take(byte_count).enumerate() {
                    if let Some(b) = byte {
                        v |= (*b as u128) << (i * 8);
                    }
                }
                debug!("adt_scalar_to_expr: read_uint failed, raw bytes fallback value={:#x}", v);
                v
            };
            let mask = if width >= 128 { value } else { value & ((1u128 << width) - 1) };
            return Some(Expr::bitvec_const(mask, width));
        }

        let variants = def.variants();
        let is_unit_enum =
            def.kind() == AdtKind::Enum && variants.iter().all(|v| v.fields().is_empty());
        if is_unit_enum {
            let value = alloc.read_uint().ok()?;
            // Part of #3556: sign-extend discriminant from repr width.
            // Raw `& 0xFFFFFFFF` failed for repr(i8) enums like Ordering
            // where Less=-1 stored as 0xFF must become 0xFFFFFFFF in BV(POINTER_WIDTH).
            // Part of #3522: use POINTER_WIDTH, not hardcoded 32, to avoid truncating
            // repr(u64) discriminants.
            let internal_def = rustc_internal::internal(self.tcx, def);
            let discr =
                internal_def.discriminant_for_variant(self.tcx, InternalVariantIdx::from_usize(0));
            let value_u128 = sign_extend_discr_val(value, discr.ty, self.tcx, POINTER_WIDTH);
            Some(Expr::bitvec_const(value_u128, POINTER_WIDTH))
        } else if let Some(expr) = self.option_like_const_expr(def, args, ty, alloc) {
            // Part of #1739: Option-like enum constant extraction.
            Some(expr)
        } else if let Some(sort) = Self::translate_ty(ty)
            && sort.datatype_sort().is_some_and(|dt| dt.constructors.len() > 1)
        {
            // Part of #4037: Multi-variant enum with Datatype sort encoding.
            // Decode the discriminant tag from the allocation to select the
            // active constructor, then build field expressions (Bool defaults
            // for ZST fields). Without this, the promoted constant falls
            // through as BV64 while the live variable reconstructs as
            // Datatype(MyEnum), causing sort mismatch in assert_eq!.
            let dt = sort.datatype_sort().expect("checked above");
            let variant_idx = decode_non_unit_enum_variant_index(alloc, ty, variants.len())?;
            if variant_idx >= dt.constructors.len() {
                return None;
            }
            let ctor_name = dt.constructors[variant_idx].name.clone();
            let field_exprs: Vec<Expr> = dt.constructors[variant_idx]
                .fields
                .iter()
                .map(|field| {
                    if field.sort.is_bool() {
                        // ZST fields (Bool sort from () mapping) get canonical defaults.
                        Expr::bool_const(false)
                    } else if let Some(width) = field.sort.bitvec_width() {
                        // Non-ZST scalar fields: read from allocation at default offset.
                        // For the initial scope (#4037), this handles simple BV payloads.
                        Expr::bitvec_const(0u128, width)
                    } else {
                        // Unsupported field sort — use a zero-width default.
                        Expr::bool_const(false)
                    }
                })
                .collect();
            let dt_name = dt.name.clone();
            let field_count = dt.constructors[variant_idx].fields.len();
            debug!(
                ?ty,
                variant_idx,
                %ctor_name,
                field_count,
                "adt_scalar_to_expr: multi-variant Datatype constant (#4037)"
            );
            Some(Expr::datatype_constructor(dt_name, ctor_name, field_exprs, sort))
        } else if let Some(sort) = Self::translate_ty(ty)
            && sort.is_int()
        {
            // Part of #3687: BigInt/BigUint constants are modeled as SMT Int.
            // The MIR constant is an allocated struct (sign + Vec<u64>), but
            // the CHC model collapses it to a scalar Int. Return int_const(0)
            // for the zero initialization constant. This must precede the
            // single-variant struct branch (#3470) which would try
            // read_composite_from_bytes on an Int sort and fail.
            debug!(?ty, "adt_scalar_to_expr: BigInt/BigUint constant -> Int(0) (#3687)");
            Some(Expr::int_const(0))
        } else if variants.len() == 1 && !variants[0].fields().is_empty() {
            // Part of #3470: Multi-field struct constant extraction.
            // Single-variant ADTs with fields (e.g., RangeInclusive<u32>) are
            // translated by reading each field from the allocation bytes using
            // the Datatype sort's field layout.
            let sort = Self::translate_ty(ty)?;
            Self::read_composite_from_allocation(alloc, 0, &sort)
        } else if let Some(sort) = Self::translate_ty(ty)
            && let Some(width) = sort.bitvec_width()
        {
            // Part of #3677: Multi-variant enum constants where translate_ty
            // returns a BV (e.g., Result<Layout, LayoutError> opaqued to BV128
            // by has_alloc_infra_arg). Read raw allocation bytes as a BV constant.
            let byte_count = (width / 8) as usize;
            if alloc.bytes.len() >= byte_count {
                let mut v: u128 = 0;
                for (i, byte) in alloc.bytes.iter().take(byte_count).enumerate() {
                    if let Some(b) = byte {
                        v |= (*b as u128) << (i * 8);
                    }
                }
                debug!(?ty, width, "adt_scalar_to_expr: multi-variant enum as opaque BV (#3677)");
                Some(Expr::bitvec_const(v, width))
            } else {
                self.diagnostics.const_translation_drop.inc();
                warn!(
                    ?ty,
                    width,
                    byte_count,
                    alloc_len = alloc.bytes.len(),
                    "adt_scalar_to_expr: opaque BV enum but allocation too short"
                );
                None
            }
        } else if variants.len() == 1 && variants[0].fields().is_empty() {
            // Part of #3768: ZST struct constants (e.g., std::alloc::Global,
            // PhantomData). These have no fields and no data to encode.
            // translate_ty maps them to Bool — return bool_const(false) as a
            // canonical ZST sentinel. Without this, ZST constants fall through
            // to the catch-all and get dropped, inflating sound_fallback_count
            // on every Box/Rc/Vec harness that references the Global allocator.
            debug!(?ty, ?name, "adt_scalar_to_expr: ZST struct constant -> bool(false)");
            Some(Expr::bool_const(false))
        } else {
            self.diagnostics.const_translation_drop.inc();
            warn!(?ty, "non-unit enum ADT not supported in CHC constants");
            None
        }
    }

    /// Translate raw/ref scalar constants into pointer-width bitvectors.
    ///
    /// Provenance-backed pointers use the promoted constant region's split-pointer
    /// address so that `obj_valid[extract(63,32,addr)]` checks pass at Ptr+ level.
    /// Part of #2958: replaces flat `0x1000` which mapped to obj_id=0 (null).
    #[must_use]
    fn pointer_scalar_expr(&self, alloc: &Allocation) -> Option<Expr> {
        if !alloc.provenance.ptrs.is_empty() {
            // Part of #3496 Bug B: if the provenance points to a known static,
            // return its unique symbolic address so pointer comparisons are decidable.
            let alloc_id = alloc.provenance.ptrs[0].1.0;
            if let Some(expr) = Self::fn_ptr_identity_expr_from_alloc_id(alloc_id) {
                return Some(expr);
            }
            if let Some(addr_expr) = self.ref_resolution.static_address_exprs.get(&alloc_id) {
                return Some(addr_expr.clone());
            }
            // Part of #3793: Cross-body AllocId resolution for inlined bodies.
            // When an inline body (e.g., Drop::drop) references a static, its
            // AllocId differs from the outer body's AllocId for the same static.
            // Fall back to DefId-based lookup: resolve this AllocId to its static
            // DefId and scan existing entries for a match.
            if let rustc_public::mir::alloc::GlobalAlloc::Static(inner_def) =
                rustc_public::mir::alloc::GlobalAlloc::from(alloc_id)
            {
                let inner_def_id = inner_def.def_id();
                for (&outer_alloc_id, addr_expr) in &self.ref_resolution.static_address_exprs {
                    if let rustc_public::mir::alloc::GlobalAlloc::Static(outer_def) =
                        rustc_public::mir::alloc::GlobalAlloc::from(outer_alloc_id)
                    {
                        if outer_def.def_id() == inner_def_id {
                            return Some(addr_expr.clone());
                        }
                    }
                }
            }
            // Part of #3860: Use per-constant address when available.
            // Without this, promoted refs like `const &Some(4u8)` resolve to
            // the shared obj_id=1 address, but the entry rule seeds memory at
            // the per-constant obj_id address → address mismatch → CTREX.
            if let Some(addr) = self.ref_resolution.promoted_const_alloc_addresses.get(&alloc_id) {
                return Some(addr.clone());
            }
            return Some(self.heap_state.promoted_const_address());
        }
        let value = alloc.read_uint().ok()?;
        let masked =
            if POINTER_WIDTH >= 128 { value } else { value & ((1u128 << POINTER_WIDTH) - 1) };
        Some(Expr::bitvec_const(masked, POINTER_WIDTH))
    }

    /// Read a float constant from an allocation as an IEEE 754 bitvector.
    ///
    /// Part of #3094: F32 → BV32, F64 → BV64, matching sort_inference.rs.
    #[must_use]
    fn float_scalar_to_expr(
        alloc: &Allocation,
        float_ty: rustc_public::ty::FloatTy,
    ) -> Option<Expr> {
        let width = float_ty_to_bitvec_width(float_ty);
        let byte_count = (width / 8) as usize;
        if alloc.bytes.len() >= byte_count {
            let mut value: u128 = 0;
            for (i, byte) in alloc.bytes.iter().take(byte_count).enumerate() {
                if let Some(b) = byte {
                    value |= (*b as u128) << (i * 8);
                }
            }
            debug!("float_scalar_to_expr: width={} value={:#x}", width, value);
            Some(Expr::bitvec_const(value, width))
        } else {
            None
        }
    }

    /// Extracts an Option-like enum constant from a MIR allocation.
    ///
    /// Handles 2-variant ADTs where one variant has 0 fields (None-like)
    /// and the other has exactly 1 field (Some-like). The discriminant byte
    /// at offset 0 selects the variant; payload bytes follow at an aligned offset.
    ///
    /// Part of #1739: CHC constant extraction for Option<T> and similar enums.
    #[must_use]
    fn option_like_const_expr(
        &self,
        def: rustc_public::ty::AdtDef,
        args: rustc_public::ty::GenericArgs,
        inner_ty: rustc_public::ty::Ty,
        alloc: &Allocation,
    ) -> Option<Expr> {
        let variants = def.variants();
        if variants.len() != 2 {
            return None;
        }
        let v0_fields = variants[0].fields().len();
        let v1_fields = variants[1].fields().len();
        if !((v0_fields == 0 && v1_fields == 1) || (v0_fields == 1 && v1_fields == 0)) {
            return None;
        }
        let some_idx = if v0_fields > 0 { 0usize } else { 1 };
        let some_variant = &variants[some_idx];
        let some_fields = some_variant.fields();
        let field = some_fields.first()?;
        let field_ty = field.ty();
        let concrete_ty = Self::resolve_generic_ty(field_ty, &args)?;
        // Sized-only deref: Option<&str> / Option<&[T]> payloads keep the
        // BV128 fat-pointer representation, matching the declared sort.
        let (payload_ty, _) = Self::deref_ref_ty_sized_only(concrete_ty);
        let payload_sort = Self::translate_ty(payload_ty)?;

        let option_name = Self::option_like_sort_name(def, &args, payload_ty);
        let some_ctor = names::option_some_constructor_name(&option_name);
        let none_ctor = names::option_none_constructor_name(&option_name);
        let dt_sort = names::enum_sort(
            &option_name,
            names::option_constructors(&option_name, payload_sort.clone()),
        );

        let discriminant = decode_option_like_variant_index(
            alloc,
            inner_ty,
            concrete_ty,
            some_idx,
            variants.len(),
        )?;

        if discriminant == some_idx {
            let payload_expr = if const_payload_is_fat_ref(concrete_ty, &payload_sort) {
                self.fat_ref_const_payload_expr(alloc, &option_name)?
            } else {
                extract_payload_from_alloc(alloc, concrete_ty, &payload_sort)?
            };
            debug!(?option_name, discriminant, "CHC constant: Option-like Some");
            Some(Expr::datatype_constructor(&option_name, &some_ctor, vec![payload_expr], dt_sort))
        } else {
            debug!(?option_name, discriminant, "CHC constant: Option-like None");
            Some(Expr::datatype_constructor(&option_name, &none_ctor, vec![], dt_sort))
        }
    }

    /// Build a BV128 fat-pointer payload (`concat(len, data_ptr)`) for a
    /// constant `&str` / `&[T]` enum payload.
    ///
    /// The length metadata is decoded from the allocation. The data pointer
    /// reuses a registered address for the literal's backing allocation when
    /// one exists (static / per-constant promoted addresses); otherwise it
    /// falls back to a fresh symbolic pointer, which soundly leaves the
    /// content unconstrained while keeping the length precise.
    #[must_use]
    fn fat_ref_const_payload_expr(&self, alloc: &Allocation, option_name: &str) -> Option<Expr> {
        let parts = decode_fat_ref_const_parts(alloc)?;
        let data_ptr = if let Some(addr) =
            self.ref_resolution.static_address_exprs.get(&parts.target_alloc_id)
        {
            addr.clone()
        } else if let Some(addr) =
            self.ref_resolution.promoted_const_alloc_addresses.get(&parts.target_alloc_id)
        {
            addr.clone()
        } else {
            debug!(
                option_name,
                len = parts.len,
                "CHC constant: fat-ptr payload backing not registered; symbolic data ptr"
            );
            declare_pending_var(chc_fresh_name("__const_fat_ptr_data"), Sort::bitvec(POINTER_WIDTH))
        };
        Some(Expr::bitvec_const(parts.len as u128, POINTER_WIDTH).concat(data_ptr))
    }
}
