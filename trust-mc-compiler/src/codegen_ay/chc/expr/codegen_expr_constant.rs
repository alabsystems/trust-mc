// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Constant translation helpers for CHC expression codegen.
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.

use crate::codegen_ay::chc::codegen_ctx::{Havoc, sound_havoc};
use crate::codegen_ay::shared::mono_ty;
use crate::kani_middle::std_abstraction::{NativeWrapperKind, native_wrapper_kind};
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;
use rustc_public::mir::ConstOperand;
use rustc_public::ty::{AdtKind, ConstantKind, RigidTy, TyConstKind, TyKind};
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
    const_payload_is_fat_ref, fat_ref_const_ref, fieldless_enum_const_bits,
    read_enum_variant_field_const,
};
pub(in crate::codegen_ay::chc) use super::codegen_expr_constant_payload::{
    decode_non_unit_enum_variant_index, decode_option_like_variant_index,
    extract_payload_from_alloc,
};
use super::codegen_types::CodegenTypes;
use crate::codegen_ay::chc::chc_fresh_name;
use crate::codegen_ay::shared::const_pointer::{self, ConstPtr, ConstRead, Slot};

#[path = "codegen_expr_constant_value.rs"]
mod value;

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

        // A constant's own bytes enter through `const_pointer::const_bytes`,
        // the one entry point; everything else is a ZST or not evaluated.
        if let Some(bytes) = const_pointer::const_bytes(mir_const) {
            return self.scalar_to_expr(&bytes, ty);
        }
        match mir_const.kind() {
            ConstantKind::Ty(ty_const) if matches!(ty_const.kind(), TyConstKind::ZSTValue(_)) => {
                canonical_zst_expr(ty).or_else(|| Some(Expr::bool_const(true)))
            }
            ConstantKind::ZeroSized => {
                canonical_zst_expr(ty).or_else(|| Some(Expr::bool_const(true)))
            }
            _ => None,
        }
    }

    fn translate_constant_referent(&self, const_op: &ConstOperand) -> Option<Expr> {
        use crate::codegen_ay::shared::const_pointer::{self, ConstTarget};

        let mir_const = &const_op.const_;
        let inner_ty = match mir_const.ty().kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
            _ => return None,
        };
        let bytes = const_pointer::const_bytes(mir_const)?;
        let r = const_pointer::const_ref(&bytes, 0, inner_ty)?;
        // Pointer constants targeting a static (e.g. `const {alloc1: *mut i32}`
        // for `static mut CELL` inside inlined drop glue) must resolve to the
        // static's ADDRESS, not its initial VALUE. Substituting the initializer
        // here evaluated the rustc-inserted null/align UB checks of inlined
        // bodies on address 0, fabricating "Genuine" counterexamples on safe
        // programs (Drop/drop_boxed_dyn.rs), and routed stores to address 0 so
        // static state vars were never updated. Return None so the caller
        // falls through to translate_constant → pointer_scalar_expr, which
        // resolves the static's ONE object address. This also covers foreign
        // (`extern`) statics, whose missing initializer body previously needed
        // a special case to avoid an eval_initializer() span_bug.
        if matches!(r.ptr.kind(), ConstTarget::Static(_)) {
            return None;
        }
        // The pointee is the WINDOW at the pointer's offset, never the target
        // from byte 0 (`const_pointer::fixed_pointee`).
        let (_, window) = const_pointer::fixed_pointee(self.tcx, &bytes, 0, inner_ty)?;
        self.scalar_to_expr(&window, inner_ty)
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Converts a scalar allocation to a AY expression based on its type.
    #[must_use]
    fn scalar_to_expr(&self, alloc: &dyn ConstRead, ty: rustc_public::ty::Ty) -> Option<Expr> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Bool) => Some(Expr::bool_const(alloc.read_bool_at(0)?)),
            TyKind::RigidTy(RigidTy::Int(int_ty)) => {
                let width = int_ty_to_bitvec_width(int_ty);
                let value = alloc.read_uint_at(0, (width / 8) as usize)?;
                Some(Expr::bitvec_const(value, width))
            }
            TyKind::RigidTy(RigidTy::Uint(uint_ty)) => {
                let width = uint_ty_to_bitvec_width(uint_ty);
                let value = alloc.read_uint_at(0, (width / 8) as usize)?;
                Some(Expr::bitvec_const(value, width))
            }
            TyKind::RigidTy(RigidTy::Tuple(_)) => {
                let value = Self::translate_ty(ty)
                    .and_then(|sort| self.read_const_safe_value(alloc, 0, ty, &sort, 0));
                if value.is_none() {
                    // Tuples previously reached the unsupported-type arm.
                    // Preserve its debt when this exact reader declines.
                    self.diagnostics.const_translation_drop.inc();
                    warn!(?ty, "unhandled constant tuple value in CHC");
                }
                value
            }
            // Fix #1898, #1905, #1229: Handle ADT (struct/enum) constants
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                if self.const_safe_value_supported(ty, 0) {
                    let sort = Self::translate_ty(ty)?;
                    self.read_const_safe_value(alloc, 0, ty, &sort, 0)
                } else {
                    self.adt_scalar_to_expr(alloc, ty, def, args)
                }
            }
            TyKind::RigidTy(RigidTy::Char) => {
                let value = alloc.read_uint_at(0, 4)?;
                Some(Expr::bitvec_const(value, 32))
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
                let len_expr = match fat_ref_const_ref(alloc, 0, pointee).and_then(|r| r.metadata) {
                    Some(len) => Expr::bitvec_const(u128::from(len), POINTER_WIDTH),
                    None => Havoc::mint_deferred(
                        self,
                        sound_havoc::UNTRACKED_CONSTANT_BYTES,
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
                // Every element under the slot clause: a pointer element is its
                // relocation's address (D8), never its offset bytes.
                self.read_composite_from_allocation(alloc, 0, &array_sort)
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
        alloc: &dyn ConstRead,
        ty: rustc_public::ty::Ty,
        def: rustc_public::ty::AdtDef,
        args: rustc_public::ty::GenericArgs,
    ) -> Option<Expr> {
        let name = def.trimmed_name();

        if matches!(
            native_wrapper_kind(self.tcx, def),
            Some(NativeWrapperKind::NonNull | NativeWrapperKind::Unique)
        ) {
            // A real pointer wrapper carries the relocation's address. A
            // user NonNull has ordinary fields and takes the ADT reader below.
            return self.pointer_scalar_expr(alloc);
        }

        // Part of #2075: Opaque ADT types, each read under the slot clause.
        match name.as_str() {
            "Alignment" => {
                let value = alloc.read_uint_at(0, (POINTER_WIDTH / 8) as usize)?;
                return Some(Expr::bitvec_const(value, POINTER_WIDTH));
            }
            // `{ size: usize, align: Alignment }`: two data words.
            "Layout" => return Some(Expr::bitvec_const(alloc.read_uint_at(0, 16)?, 128)),
            // Rustc stores a TypeId as pointers into a type-id segment whose
            // OFFSETS are the hash words (`ConstPtr::offset`); older layouts
            // store plain data.
            "TypeId" => {
                let value = match (alloc.stored_pointer(0), alloc.stored_pointer(8)) {
                    (Some(lo), Some(hi)) => {
                        u128::from(lo.offset()) | (u128::from(hi.offset()) << 64)
                    }
                    _ => alloc.read_uint_at(0, 16)?,
                };
                return Some(Expr::bitvec_const(value, 128));
            }
            _ => {}
        }

        let variants = def.variants();
        let is_unit_enum =
            def.kind() == AdtKind::Enum && variants.iter().all(|v| v.fields().is_empty());
        if is_unit_enum {
            // Part of #3556 / #3522: the discriminant at POINTER_WIDTH, sign-
            // extended as the aggregate path does. Sign-extending the raw tag
            // from the DISCRIMINANT type's width left a default-repr
            // `enum G { N = -1 }` (discriminant type `isize`, one-byte tag) at
            // `0xFF`; the tag is decoded from its own width instead.
            let value_u128 = fieldless_enum_const_bits(ty, alloc, 0, POINTER_WIDTH)?;
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
            let bytes = alloc;
            let resolve = |ptr: &ConstPtr| self.const_ptr_address(ptr).map(|a| a.into_expr());
            let variant_idx = decode_non_unit_enum_variant_index(bytes, ty, variants.len())?;
            if variant_idx >= dt.constructors.len() {
                return None;
            }
            let ctor_name = dt.constructors[variant_idx].name.clone();
            // READ the active variant's fields. Zero-filling them fabricated the
            // constant: `Ok(Ordering::Greater)` became `Ok(0)`, a joined `o`
            // compared unequal to it, and `!(o == Ok(Ordering::Greater))` was
            // proved (tools/soundness-duals/negative/joined_enum_constant_payloads.rs).
            // A field the reader cannot decode drops the constant, which then
            // stays unconstrained.
            let mut field_exprs: Vec<Expr> =
                Vec::with_capacity(dt.constructors[variant_idx].fields.len());
            for (field_idx, field) in dt.constructors[variant_idx].fields.iter().enumerate() {
                let Some(field_expr) = read_enum_variant_field_const(
                    bytes,
                    ty,
                    variant_idx,
                    field_idx,
                    &field.sort,
                    &resolve,
                ) else {
                    self.diagnostics.const_translation_drop.inc();
                    warn!(
                        ?ty,
                        variant_idx,
                        field_idx,
                        "adt_scalar_to_expr: multi-variant constant field not decodable; constant dropped"
                    );
                    return None;
                };
                field_exprs.push(field_expr);
            }
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
            // translated by reading each field from the allocation bytes.
            //
            // The field offsets come from rustc's LAYOUT, not from
            // declaration-order packing: `repr(Rust)` reorders fields, and
            // `RangeInclusive<u8>` really is laid out `start@0, exhausted@1,
            // end@2`, so the sequential reader decoded `0..=1` as
            // `start=0, end=0, exhausted=true`.
            let sort = Self::translate_ty(ty)?;
            self.read_adt_composite_from_allocation(alloc, 0, ty, &sort)
        } else if let Some(sort) = Self::translate_ty(ty)
            && let Some(width) = sort.bitvec_width()
        {
            // Part of #3677: Multi-variant enum constants where translate_ty
            // returns a BV (e.g., Result<Layout, LayoutError> opaqued to BV128
            // by has_alloc_infra_arg). Read raw allocation bytes as a BV constant.
            // Uninitialized bytes (padding) read as 0; a relocation declines.
            if let Some(v) = alloc.read_uint_zero_filled(0, width) {
                debug!(?ty, width, "adt_scalar_to_expr: multi-variant enum as opaque BV (#3677)");
                Some(Expr::bitvec_const(v, width))
            } else {
                self.diagnostics.const_translation_drop.inc();
                warn!(
                    ?ty,
                    width,
                    alloc_len = alloc.len(),
                    "adt_scalar_to_expr: opaque BV enum not readable as data"
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
    /// A constant pointer is the relocation at its own byte 0 plus the offset
    /// its bytes carry (`shared::const_pointer`): its address is the target's
    /// ONE object base plus that offset (`const_ptr_address`). A target the
    /// object table never minted has no address here: the constant is dropped
    /// (recorded), never placed at another object's base. A constant with no
    /// relocation is an integer address (`NonNull::dangling()`, null).
    #[must_use]
    fn pointer_scalar_expr(&self, alloc: &dyn ConstRead) -> Option<Expr> {
        match alloc.read_slot(0, POINTER_WIDTH) {
            Slot::Pointer(ptr) => match self.const_ptr_address(&ptr) {
                Some(addr) => Some(addr.into_expr()),
                None => {
                    self.diagnostics.const_translation_drop.inc();
                    warn!(?ptr, "constant pointer target has no object in this harness; dropped");
                    None
                }
            },
            Slot::Data(value) => Some(Expr::bitvec_const(value, POINTER_WIDTH)),
            Slot::Uninit | Slot::PartialPointer | Slot::OutOfBounds => None,
        }
    }

    /// Read a float constant from an allocation as an IEEE 754 bitvector.
    ///
    /// Part of #3094: F32 → BV32, F64 → BV64, matching sort_inference.rs.
    #[must_use]
    fn float_scalar_to_expr(
        alloc: &dyn ConstRead,
        float_ty: rustc_public::ty::FloatTy,
    ) -> Option<Expr> {
        let width = float_ty_to_bitvec_width(float_ty);
        let value = alloc.read_uint_at(0, (width / 8) as usize)?;
        debug!("float_scalar_to_expr: width={} value={:#x}", width, value);
        Some(Expr::bitvec_const(value, width))
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
        alloc: &dyn ConstRead,
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
        let concrete_ty = mono_ty::field_ty(field, &args)?;
        // Sized-only deref: Option<&str> / Option<&[T]> payloads keep the
        // BV128 fat-pointer representation, matching the declared sort.
        let (payload_ty, _) = Self::deref_ref_ty_sized_only(concrete_ty);
        let payload_sort = Self::translate_ty(payload_ty)?;

        let option_name = Self::option_like_sort_name(def, &args, payload_ty);
        let some_ctor = names::option_some_constructor_name(&option_name);
        let none_ctor = names::option_none_constructor_name(&option_name);
        let dt_sort = names::enum_sort(
            &option_name,
            Self::option_like_constructors(def, &option_name, payload_sort.clone()),
        );

        let bytes = alloc;
        let discriminant = decode_option_like_variant_index(
            bytes,
            inner_ty,
            concrete_ty,
            some_idx,
            variants.len(),
        )?;

        if discriminant == some_idx {
            let payload_expr = if const_payload_is_fat_ref(concrete_ty, &payload_sort) {
                self.fat_ref_const_payload_expr(
                    alloc,
                    inner_ty,
                    some_idx,
                    concrete_ty,
                    &option_name,
                )?
            } else {
                let resolve = |ptr: &ConstPtr| self.const_ptr_address(ptr).map(|a| a.into_expr());
                extract_payload_from_alloc(
                    bytes,
                    inner_ty,
                    some_idx,
                    concrete_ty,
                    &payload_sort,
                    &resolve,
                )?
            };
            debug!(?option_name, discriminant, "CHC constant: Option-like Some");
            Some(Expr::datatype_constructor(&option_name, &some_ctor, vec![payload_expr], dt_sort))
        } else {
            debug!(?option_name, discriminant, "CHC constant: Option-like None");
            Some(Expr::datatype_constructor(&option_name, &none_ctor, vec![], dt_sort))
        }
    }

    /// Build a BV128 fat-pointer payload (`concat(len, data_ptr)`) for a
    /// constant `&str` / `&[T]` enum payload stored in `alloc`.
    ///
    /// The payload's slot sits at its variant's field offset, not at byte 0:
    /// the data pointer is the relocation STARTING there (plus its offset),
    /// and the length is the word beside it (`const_pointer::const_ref`). A
    /// data pointer whose target has no object drops the payload.
    #[must_use]
    fn fat_ref_const_payload_expr(
        &self,
        alloc: &dyn ConstRead,
        enum_ty: rustc_public::ty::Ty,
        variant_idx: usize,
        payload_ty: rustc_public::ty::Ty,
        option_name: &str,
    ) -> Option<Expr> {
        let TyKind::RigidTy(RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _)) =
            payload_ty.kind()
        else {
            return None;
        };
        let slot = crate::kani_middle::abi::LayoutOf::new(enum_ty)
            .variant_field_offset(variant_idx, 0)
            .unwrap_or(0);
        let r = fat_ref_const_ref(alloc, slot, pointee)?;
        let Some(data_ptr) = self.const_ptr_address(&r.ptr) else {
            debug!(option_name, "CHC constant: fat-ptr payload target has no object; dropped");
            return None;
        };
        let len = r.metadata?;
        Some(Expr::bitvec_const(u128::from(len), POINTER_WIDTH).concat(data_ptr.into_expr()))
    }
}
