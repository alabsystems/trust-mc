// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! ADT aggregate codegen for AY — dispatch and enum handling.
//!
//! Extracted from `aggregate.rs` to reduce file size (#2246).
//! Handles construction of ADT values in SMT encoding:
//! - Transparent wrappers: NonNull, Unique, NonZero
//! - Unit enums: discriminant bitvectors
//! - Option-like enums: 2-variant datatypes with optional payload
//! - General enums: multi-variant datatypes
//!
//! Struct aggregate handling is in `aggregate_struct.rs`.

use ay_bindings::Expr;
use rustc_abi::VariantIdx as InternalVariantIdx;
use rustc_public::CrateDef;
use rustc_public::mir::Operand;
use rustc_public::rustc_internal;
use rustc_public::ty::{AdtDef, AdtKind, GenericArgs, VariantIdx};
use rustc_public_bridge::IndexedVal;
use tracing::{debug, warn};

use crate::codegen_ay::chc::codegen_stmt_aggregate_adt::sign_extend_discr_val;
use crate::codegen_ay::types::{
    SignExtension, coerce_bitvec_width_safe, coerce_bool_to_unit_datatype,
};

use super::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen ADT (enum/struct) aggregate construction.
    ///
    /// Supported patterns:
    /// - Unit enums: all variants have no fields → discriminant as bitvector constant
    /// - Option-like enums: exactly 2 variants, one with 0 fields, one with 1 field
    /// - General enums: any number of variants with any number of fields
    /// - Structs: single variant with any number of fields
    ///
    /// Returns None for unsupported ADT patterns (e.g., unions).
    ///
    /// REQUIRES: def is a valid AdtDef from MIR
    /// REQUIRES: variant_idx is a valid index into def.variants()
    /// ENSURES: On Some, result encodes ADT value (datatype or bitvector for unit enums)
    /// ENSURES: On None, unsupported diagnostic recorded for complex enums
    pub(super) fn codegen_adt_aggregate(
        &mut self,
        def: AdtDef,
        variant_idx: VariantIdx,
        args: GenericArgs,
        operands: &[Operand],
    ) -> Option<Expr> {
        let variants = def.variants();
        let adt_name = Self::adt_sort_name(def, &args);

        let base_name = def.trimmed_name();
        debug!(
            "codegen_adt_aggregate: adt={}, base_name={}, variant_idx={}, num_variants={}, operands={}",
            adt_name,
            base_name,
            variant_idx.to_index(),
            variants.len(),
            operands.len()
        );

        // Debug variant field counts
        for (i, v) in variants.iter().enumerate() {
            debug!("  variant[{}] '{}': {} fields", i, v.name(), v.fields().len());
        }

        // Part of #912: NonNull/Unique are repr(transparent) pointer wrappers.
        if let Some(expr) = self.try_codegen_transparent_wrapper(&base_name, def, &args, operands) {
            return Some(expr);
        }
        if matches!(
            base_name.as_str(),
            "NonNull"
                | "Unique"
                | "NonZero"
                | "ManuallyDrop"
                | "MaybeUninit"
                | "UnsafeCell"
                | "Cell"
                | "Mutex"
                | "RwLock"
                | "ArcInner"
                | "Box"
                | "Rc"
                | "Arc"
        ) {
            // try_codegen_transparent_wrapper returned None — log the unexpected case
            warn!(
                "codegen_adt_aggregate: {} transparent wrapper returned None with {} operands",
                base_name,
                operands.len()
            );
            return None;
        }

        // Check if this is a unit enum (all variants have no fields).
        // Must be a real enum (>1 variant) — ZST structs also have no fields
        // but calling discriminant_for_variant on a struct panics.
        let is_unit_enum = variants.len() > 1 && variants.iter().all(|v| v.fields().is_empty());

        if is_unit_enum && operands.is_empty() {
            return self.codegen_unit_enum_discriminant(def, variant_idx, variants.len());
        }

        // Check for Option-like enum: exactly 2 variants, one with 0 fields, one with 1 field
        if variants.len() == 2 {
            let v0_fields = variants[0].fields().len();
            let v1_fields = variants[1].fields().len();

            debug!("  Checking Option-like: v0_fields={}, v1_fields={}", v0_fields, v1_fields);

            if (v0_fields == 0 && v1_fields == 1) || (v0_fields == 1 && v1_fields == 0) {
                return self.codegen_option_like_enum(
                    def,
                    variant_idx,
                    args,
                    operands,
                    &adt_name,
                    &variants,
                );
            }
        }

        // Handle general enums with payload variants (Result-like and beyond).
        if def.kind() == AdtKind::Enum {
            return self.codegen_general_enum(def, variant_idx, args, operands, &adt_name);
        }

        // Handle structs: single variant with fields
        if def.kind() == AdtKind::Struct {
            return self.codegen_struct_aggregate(def, variant_idx, args, operands, &adt_name);
        }

        // Not a supported ADT pattern
        let location = format!(
            "ADT aggregate '{}' with {} variants, {} operands",
            adt_name,
            variants.len(),
            operands.len()
        );
        self.ctx.unsupported("Aggregate::Adt", location);
        None
    }

    /// Try to codegen transparent wrapper types.
    /// Returns Some(expr) if the type matches and operand count is valid.
    ///
    /// Part of #4067: Extended to handle Mutex/RwLock/Cell/UnsafeCell/ArcInner
    /// (data-extract wrappers) and Box/Rc/Arc (pointer wrappers), mirroring the
    /// CHC encoding in codegen_stmt_aggregate_wrapper.rs.
    fn try_codegen_transparent_wrapper(
        &mut self,
        base_name: &str,
        def: AdtDef,
        args: &GenericArgs,
        operands: &[Operand],
    ) -> Option<Expr> {
        match base_name {
            "NonNull" | "NonZero" => {
                if operands.len() == 1 {
                    let expr = self.codegen_operand(&operands[0])?;
                    debug!(
                        "codegen_adt_aggregate: {} transparent wrapper → returning operand directly",
                        base_name
                    );
                    Some(expr)
                } else {
                    None
                }
            }
            "Unique" => {
                if operands.len() == 1 {
                    let expr = self.codegen_operand(&operands[0])?;
                    debug!(
                        "codegen_adt_aggregate: Unique transparent wrapper → returning operand directly"
                    );
                    Some(expr)
                } else if operands.len() == 2 {
                    // Unique { pointer: NonNull<T>, _marker: PhantomData<T> }
                    // Take the first operand (NonNull pointer), ignore PhantomData
                    let expr = self.codegen_operand(&operands[0])?;
                    debug!(
                        "codegen_adt_aggregate: Unique with 2 operands → returning pointer, ignoring PhantomData"
                    );
                    Some(expr)
                } else {
                    None
                }
            }
            // Part of #4067: ManuallyDrop, MaybeUninit, UnsafeCell, Cell — single-operand
            // passthrough. Transparent in verification model.
            //
            // Uninitialized construction (`MaybeUninit::uninit()`): the single
            // operand is the union's uninitialized `()` field, whose sort is NOT
            // the inner type, so a plain passthrough would yield a unit-sorted
            // value (and break the enclosing struct aggregate). Uninitialized
            // memory is EXACTLY an arbitrary value of the inner type, so declare a
            // fresh unconstrained value of the inner sort. This is the precise
            // model — universally quantified over all possible uninit contents
            // (sound for proofs), and any later element store/read threads through
            // this value. `MaybeUninit::new(v)`/`ManuallyDrop::new(v)` carry the
            // inner value as the operand (sort matches the inner type) and pass
            // through unchanged.
            "ManuallyDrop" | "MaybeUninit" | "UnsafeCell" | "Cell" => {
                if operands.len() != 1 {
                    return None;
                }
                let op = self.codegen_operand(&operands[0]);
                match Self::infer_wellknown_adt_from_ty(def, args) {
                    // Inner sort known (MaybeUninit/ManuallyDrop): pass the operand
                    // through when it carries the inner value (sorts match); else it
                    // is the uninitialized `()` field → fresh arbitrary inner value.
                    Some(inner) => {
                        if matches!(&op, Some(e) if e.sort() == &inner) {
                            debug!(
                                "codegen_adt_aggregate: {} transparent wrapper → operand directly",
                                base_name
                            );
                            op
                        } else {
                            let name = self.ctx.fresh_name("maybe_uninit");
                            debug!(
                                "codegen_adt_aggregate: {} uninitialized field → fresh {:?} (uninit = arbitrary inner value)",
                                base_name,
                                inner.datatype_name()
                            );
                            Some(self.ctx.declare_var(&name, inner))
                        }
                    }
                    // No inner sort inferable (e.g. UnsafeCell/Cell): transparent
                    // passthrough of the single operand (None stays None, fail closed).
                    None => op,
                }
            }
            // Part of #4067: Mutex/RwLock/ArcInner — data-extract wrappers. The meaningful
            // data is the last operand (UnsafeCell<T> for Mutex/RwLock, T for ArcInner).
            // Other fields (poison flag, lock state, ref counts) are irrelevant in
            // single-threaded verification.
            "Mutex" | "RwLock" | "ArcInner" => {
                if operands.is_empty() {
                    return None;
                }
                let data_idx = operands.len() - 1;
                let expr = self.codegen_operand(&operands[data_idx])?;
                debug!(
                    "codegen_adt_aggregate: {} data-extract wrapper → returning last field (idx {})",
                    base_name, data_idx
                );
                Some(expr)
            }
            // Part of #4067: Box/Rc/Arc — pointer wrappers. First operand is the pointer;
            // remaining operands (PhantomData, allocator) are metadata.
            "Box" | "Rc" | "Arc" => {
                if operands.is_empty() {
                    return None;
                }
                let expr = self.codegen_operand(&operands[0])?;
                debug!(
                    "codegen_adt_aggregate: {} pointer wrapper → returning first operand, ignoring {} metadata fields",
                    base_name,
                    operands.len() - 1
                );
                Some(expr)
            }
            _ => None,
        }
    }

    /// Codegen unit enum discriminant as bitvector constant.
    fn codegen_unit_enum_discriminant(
        &mut self,
        def: AdtDef,
        variant_idx: VariantIdx,
        num_variants: usize,
    ) -> Option<Expr> {
        // For unit enums, return the actual discriminant value (not variant index).
        // Bug fix (#1393): Enums with explicit discriminants like `A = -500` need
        // the actual value, not the variant index.
        let internal_def = rustc_internal::internal(self.ctx.tcx, def);
        let variant_idx_internal = InternalVariantIdx::from_usize(variant_idx.to_index());
        let discr = internal_def.discriminant_for_variant(self.ctx.tcx, variant_idx_internal);

        // Use fixed bit width to match sort_inference.rs (which doesn't have tcx).
        // 32 bits handles common cases; 64 for very large enums.
        let bits = if num_variants <= 65536 { 32 } else { 64 };
        // Part of #3543: Sign-extend signed discriminants (CHC parity for #3536).
        let discriminant_val = sign_extend_discr_val(discr.val, discr.ty, self.ctx.tcx, bits);
        Some(Expr::bitvec_const(discriminant_val, bits))
    }

    /// Codegen Option-like enum (exactly 2 variants, one with 0 fields, one with 1 field).
    fn codegen_option_like_enum(
        &mut self,
        _def: AdtDef,
        variant_idx: VariantIdx,
        args: GenericArgs,
        operands: &[Operand],
        adt_name: &str,
        variants: &[rustc_public::ty::VariantDef],
    ) -> Option<Expr> {
        let variant = &variants[variant_idx.to_index()];
        let variant_has_field = !variant.fields().is_empty();

        // Get the sort for this ADT (need args for generic param resolution)
        let sort = Self::infer_adt_sort(_def, args)?;

        // Option-like enums must be encoded as datatypes. If this ADT maps to Int,
        // we would lose discriminant information and later Option handling would fail.
        if sort.is_int() {
            self.ctx.unsupported(
                "Aggregate::Adt",
                format!("Option-like enum '{}' mapped to Int sort", adt_name),
            );
            return None;
        }
        if !sort.is_datatype() {
            self.ctx.unsupported(
                "Aggregate::Adt",
                format!("Option-like enum '{}' mapped to non-datatype sort {:?}", adt_name, sort),
            );
            return None;
        }

        if variant_has_field {
            // This is the "Some" variant - construct with payload
            if operands.len() != 1 {
                self.ctx.unsupported(
                    "Aggregate::Adt",
                    format!("Some variant expected 1 operand, got {}", operands.len()),
                );
                return None;
            }

            // #824: Apply value semantics for reference payloads.
            let payload = self.get_option_payload_value(&operands[0])?;

            // Part of #2549: Use scoped constructor names to avoid Z3
            // "ambiguous function declaration" with multiple Option instantiations.
            let some_name = crate::codegen_ay::names::option_some_constructor_name(adt_name);
            debug!("  Constructing Some variant '{}' with payload", some_name);

            // Debug: log ref_pointees for Option<&T> (#703).
            if let Operand::Copy(src_place) | Operand::Move(src_place) = &operands[0] {
                let src_base = self.ssa_base_name(src_place);
                if let Some(pointee) = self.ref_pointees.get(src_base.as_str()).cloned() {
                    debug!(
                        "codegen_adt_aggregate: ref payload {} has pointee {}",
                        src_base, pointee
                    );
                }
            }

            Some(Expr::datatype_constructor(adt_name, some_name, vec![payload], sort))
        } else {
            // This is the "None" variant - construct without payload
            if !operands.is_empty() {
                self.ctx.unsupported(
                    "Aggregate::Adt",
                    format!("None variant expected 0 operands, got {}", operands.len()),
                );
                return None;
            }
            let none_name = crate::codegen_ay::names::option_none_constructor_name(adt_name);
            debug!("  Constructing None variant '{}'", none_name);
            Some(Expr::datatype_constructor(adt_name, none_name, vec![], sort))
        }
    }

    /// Codegen general enum variant construction (Result-like and beyond).
    fn codegen_general_enum(
        &mut self,
        def: AdtDef,
        variant_idx: VariantIdx,
        args: GenericArgs,
        operands: &[Operand],
        adt_name: &str,
    ) -> Option<Expr> {
        let variants = def.variants();
        let variant = &variants[variant_idx.to_index()];
        let expected_fields = variant.fields().len();

        debug!(
            "  General enum '{}' variant '{}' with {} fields, {} operands",
            adt_name,
            variant.name(),
            expected_fields,
            operands.len()
        );

        if operands.len() != expected_fields {
            self.ctx.unsupported(
                "Aggregate::Adt",
                format!(
                    "Enum '{}' variant '{}' expected {} fields, got {} operands",
                    adt_name,
                    variant.name(),
                    expected_fields,
                    operands.len()
                ),
            );
            return None;
        }

        // Get the sort for this ADT (need args for generic param resolution)
        // Clone args since infer_adt_sort takes ownership but we need args below for field coercion.
        let sort = Self::infer_adt_sort(def, args.clone())?;

        // #918, #926: BigInt/BigUint/Ratio types return Int sort - handle specially
        if sort.is_int() {
            return self.codegen_bigint_aggregate(adt_name, &sort);
        }
        if !sort.is_datatype() {
            self.ctx.unsupported(
                "Aggregate::Adt",
                format!(
                    "Enum '{}' variant '{}' mapped to non-datatype sort {:?}",
                    adt_name,
                    variant.name(),
                    sort
                ),
            );
            return None;
        }

        // Codegen all field values, coercing sorts to match the declared datatype fields.
        // Part of #3094: ZST fields (e.g., `Unit` enum) translate to Bool operands but the
        // datatype constructor expects BitVec(32) (the unit-enum discriminant encoding).
        let variant_fields = variant.fields();
        let mut field_exprs = Vec::with_capacity(operands.len());
        for (i, op) in operands.iter().enumerate() {
            if let Some(expr) = self.codegen_operand(op) {
                // Resolve the expected field sort from the variant's field type.
                let coerced = if let Some(field_def) = variant_fields.get(i) {
                    let field_ty = field_def.ty();
                    let expected_sort = Self::resolve_generic_ty(field_ty, &args)
                        .and_then(Self::infer_sort_from_ty);

                    if let Some(ref target_sort) = expected_sort {
                        if expr.sort() != target_sort {
                            if let Some(target_w) = target_sort.bitvec_width() {
                                debug!(
                                    "  Coercing field {} sort {:?} → BV({})",
                                    i,
                                    expr.sort(),
                                    target_w
                                );
                                coerce_bitvec_width_safe(expr, target_w, SignExtension::ZeroExtend)
                            } else if let Some(unit_expr) =
                                coerce_bool_to_unit_datatype(&expr, target_sort)
                            {
                                debug!("  Coercing field {} Bool → Unit datatype", i);
                                unit_expr
                            } else if let Some(singleton) =
                                Self::resolve_generic_ty(field_ty, &args)
                                    .and_then(Self::try_singleton_enum_value)
                                    .filter(|v| v.sort() == target_sort)
                            {
                                // Part of #4112 follow-up: singleton enums
                                // (`Option<Infallible>` and friends) are ZSTs
                                // whose operand codegen yields a Bool sentinel.
                                // The value is fully determined by the type —
                                // construct its sole inhabitant exactly (e.g.
                                // `ControlFlow::Break(None)` from `?` desugaring).
                                debug!(
                                    "  Coercing field {} ZST enum → sole inhabitant constructor (Part of #4112 follow-up)",
                                    i
                                );
                                singleton
                            } else {
                                // Target is non-bitvec, non-unit datatype — use expr as-is.
                                warn!(
                                    "Sort mismatch field {} of '{}::{}': expr {:?} vs expected {:?}",
                                    i,
                                    adt_name,
                                    variant.name(),
                                    expr.sort(),
                                    target_sort
                                );
                                expr
                            }
                        } else {
                            expr
                        }
                    } else {
                        expr
                    }
                } else {
                    expr
                };
                field_exprs.push(coerced);
            } else {
                self.ctx.unsupported(
                    "Aggregate::Adt",
                    format!(
                        "Failed to codegen field {} of enum '{}' variant '{}'",
                        i,
                        adt_name,
                        variant.name()
                    ),
                );
                return None;
            }
        }

        debug!(
            "  Constructing enum '{}' variant '{}' with {} fields",
            adt_name,
            variant.name(),
            field_exprs.len()
        );
        // Part of #2549: Scope Option constructor names to avoid Z3
        // "ambiguous function declaration" with multiple Option instantiations.
        let constructor_name =
            crate::codegen_ay::names::scope_option_ctor(variant.name(), adt_name);
        Some(Expr::datatype_constructor(adt_name, constructor_name, field_exprs, sort))
    }

    /// Build the sole inhabitant of a "singleton enum" — an enum with exactly
    /// one inhabited variant, which is fieldless (e.g. `Option<Infallible>`,
    /// whose only value is `None`). Such types are ZSTs, so operand codegen
    /// loses their identity; the value is fully determined by the type and can
    /// be reconstructed exactly. Returns `None` when the type doesn't have this
    /// shape or its sort isn't the matching datatype. Part of #4112 follow-up.
    pub(super) fn try_singleton_enum_value(ty: rustc_public::ty::Ty) -> Option<Expr> {
        use rustc_public::ty::TyKind;

        let TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, args)) = ty.kind() else {
            return None;
        };
        if def.kind() != AdtKind::Enum {
            return None;
        }
        let variants = def.variants();
        let mut inhabited = variants.iter().enumerate().filter(|(_, v)| {
            v.fields().iter().all(|f| {
                let field_ty = Self::resolve_generic_ty(f.ty(), &args).unwrap_or_else(|| f.ty());
                !Self::ty_is_uninhabited(field_ty, 0)
            })
        });
        let (idx, variant) = inhabited.next()?;
        if inhabited.next().is_some() || !variant.fields().is_empty() {
            return None;
        }

        let sort = Self::infer_sort_from_ty(ty)?;
        let dt = sort.datatype_sort()?;
        let ctor = dt.constructors.get(idx)?;
        if !ctor.fields.is_empty() {
            return None;
        }
        let dt_name = dt.name.clone();
        let ctor_name = ctor.name.clone();
        Some(Expr::datatype_constructor(dt_name, ctor_name, vec![], sort))
    }

    /// Conservative uninhabitedness check: returns `true` only when the type
    /// provably has no values (`!`, `Infallible`-like empty enums, and
    /// compounds containing them). Returns `false` (inhabited) when unsure —
    /// that direction only disables the singleton-enum reconstruction, never
    /// fabricates values. Part of #4112 follow-up.
    fn ty_is_uninhabited(ty: rustc_public::ty::Ty, depth: usize) -> bool {
        use rustc_public::ty::{RigidTy, TyKind};

        if depth > 8 {
            return false;
        }
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Never) => true,
            TyKind::RigidTy(RigidTy::Tuple(tys)) => {
                tys.iter().any(|t| Self::ty_is_uninhabited(*t, depth + 1))
            }
            TyKind::RigidTy(RigidTy::Adt(def, args)) => match def.kind() {
                // Enum: uninhabited iff every variant has an uninhabited field
                // (an enum with no variants is trivially uninhabited).
                AdtKind::Enum => def.variants().iter().all(|v| {
                    v.fields().iter().any(|f| {
                        let field_ty =
                            Self::resolve_generic_ty(f.ty(), &args).unwrap_or_else(|| f.ty());
                        Self::ty_is_uninhabited(field_ty, depth + 1)
                    })
                }),
                // Struct: uninhabited iff any field is uninhabited.
                AdtKind::Struct => def.variants().first().is_some_and(|v| {
                    v.fields().iter().any(|f| {
                        let field_ty =
                            Self::resolve_generic_ty(f.ty(), &args).unwrap_or_else(|| f.ty());
                        Self::ty_is_uninhabited(field_ty, depth + 1)
                    })
                }),
                // Unions and anything else: assume inhabited.
                _ => false,
            },
            _ => false,
        }
    }
}
