// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Type ABI layout information.
//!
//! Provides `LayoutOf` — a wrapper around rustc's `LayoutShape` that adds
//! convenience methods for querying type layout properties (size, alignment,
//! unsized tails, field offsets).
//!
//! Extracted from `trust_mc-compiler/src/kani_middle/abi.rs` (Part of #2997).

#[allow(unused_imports)] // Trait-backed on current rustc_public; inherent on the pinned API.
use rustc_public::CrateDefType;
use rustc_public::abi::{FieldsShape, LayoutShape, VariantsShape};
use rustc_public::ty::{AdtKind, RigidTy, Ty, TyKind, UintTy};
use tracing::debug;

/// A struct to encapsulate the layout information for a given type
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LayoutOf {
    ty: Ty,
    layout: LayoutShape,
}

impl LayoutOf {
    /// Create the layout structure for the given type.
    /// REQUIRES: ty.layout() succeeds (type has known layout in current target)
    /// ENSURES: self.layout matches ty's LayoutShape for this target
    ///
    /// # Panics
    /// Panics if the layout is not available for the given type.
    #[allow(clippy::panic)] // Documented panic - layout required for type
    pub fn new(ty: Ty) -> LayoutOf {
        let layout = ty
            .layout()
            .unwrap_or_else(|_| panic!("LayoutOf::new requires layout for `{}`", ty))
            .shape();
        LayoutOf { ty, layout }
    }

    /// Return whether the type is sized.
    pub fn is_sized(&self) -> bool {
        self.layout.is_sized()
    }

    /// Return whether the type is unsized and its tail is a foreign item.
    ///
    /// This will also return `true` if the type is foreign.
    pub fn has_foreign_tail(&self) -> bool {
        self.unsized_tail()
            .is_some_and(|t| matches!(t.kind(), TyKind::RigidTy(RigidTy::Foreign(_))))
    }

    /// Return whether the type is unsized and its tail is a trait object.
    pub fn has_trait_tail(&self) -> bool {
        self.unsized_tail().is_some_and(|t| t.kind().is_trait())
    }

    /// Return whether the type is unsized and its tail is a slice.
    pub fn has_slice_tail(&self) -> bool {
        self.unsized_tail().is_some_and(|tail| {
            let kind = tail.kind();
            kind.is_slice() || kind.is_str()
        })
    }

    /// Return the unsized tail of the type if this is an unsized type.
    ///
    /// For foreign types, return `Some(self.ty)`.
    /// For unsized types, this should return either a slice, a string slice, a dynamic type,
    /// or a foreign type.
    /// For other types, this function will return `None`.
    ///
    /// REQUIRES: self.layout was successfully computed for ty
    /// ENSURES: Some(tail) only if !self.is_sized()
    /// ENSURES: Some(tail) implies tail.kind() is Slice, Str, Dynamic, or Foreign
    pub fn unsized_tail(&self) -> Option<Ty> {
        if self.layout.is_unsized() {
            match self.ty.kind().rigid().expect("should be monomorphized") {
                RigidTy::Slice(..) | RigidTy::Dynamic(..) | RigidTy::Str => Some(self.ty),
                RigidTy::Adt(..) | RigidTy::Tuple(..) => {
                    // Recurse the tail field type until we find the unsized tail.
                    self.last_field_layout().unsized_tail()
                }
                RigidTy::Foreign(_) => Some(self.ty),
                _ => unreachable!("Expected unsized type but found `{}`", self.ty), // external enum: RigidTy
            }
        } else {
            None
        }
    }

    /// Return the type of the elements of the slice or `str` at the unsized tail of this type.
    ///
    /// For sized types and trait unsized type, this function will return `None`.
    pub fn unsized_tail_elem_ty(&self) -> Option<Ty> {
        self.unsized_tail().and_then(|tail| {
            match tail.kind().rigid().expect("should be monomorphized") {
                RigidTy::Slice(elem_ty) => Some(*elem_ty),
                // String slices have the same layout as slices of u8.
                // https://doc.rust-lang.org/reference/type-layout.html#str-layout
                RigidTy::Str => Some(Ty::unsigned_ty(UintTy::U8)),
                _ => None, // external enum: RigidTy
            }
        })
    }

    /// Return the size of the sized portion of this type.
    ///
    /// For a sized type, this function will return the size of the type.
    /// For an unsized type, this function will return the size of the sized portion including
    /// any padding bytes that lead to the unsized field.
    /// I.e.: the size of the type, excluding the trailing unsized portion.
    ///
    /// REQUIRES: self.ty has valid layout
    /// ENSURES: self.is_sized() implies return == self.layout.size.bytes()
    ///
    /// # Panics
    /// Panics when [`LayoutOf::try_size_of_head`] reports the layout malformed (see
    /// [`HeadSizeError`]). Callers that can surface an error use that method instead.
    pub fn size_of_head(&self) -> usize {
        match self.try_size_of_head() {
            Ok(size) => size,
            Err(err) => panic!("size_of_head: {err} for `{}`", self.ty),
        }
    }

    /// Return the size of the sized portion of this type, or why it cannot be measured.
    ///
    /// The total form of [`LayoutOf::size_of_head`]: a layout that violates rustc's
    /// invariants (an unsized type of a kind that carries no unsized tail, an unsized
    /// struct or tuple without arbitrary field offsets, or a tail offset whose sum with the
    /// tail's head size leaves `usize`) is reported, never wrapped or assumed away.
    ///
    /// ENSURES: self.is_sized() implies return == Ok(self.layout.size.bytes())
    pub fn try_size_of_head(&self) -> Result<usize, HeadSizeError> {
        if self.is_sized() {
            return Ok(self.layout.size.bytes());
        }
        match self.ty.kind().rigid() {
            None => Err(HeadSizeError::NotMonomorphized),
            Some(
                RigidTy::Slice(_) | RigidTy::Str | RigidTy::Dynamic(..) | RigidTy::Foreign(..),
            ) => Ok(0),
            Some(RigidTy::Adt(..) | RigidTy::Tuple(..)) => {
                let unsized_offset_unadjusted = unsized_tail_offset(&self.layout.fields)?;
                debug!(ty=?self.ty, ?unsized_offset_unadjusted, "size_of_sized_portion");
                let tail_head = self.last_field_layout().try_size_of_head()?;
                head_size_with_tail(unsized_offset_unadjusted, tail_head)
            }
            Some(_) => Err(HeadSizeError::UnexpectedUnsizedKind), // external enum: RigidTy
        }
    }

    /// Return the alignment of the fields that are sized from the head of the object.
    ///
    /// For a sized type, this function will return the alignment of the type.
    /// For an unsized type, this function will return the alignment of the sized portion.
    ///
    /// REQUIRES: self.ty has valid layout
    /// ENSURES: return >= 1 (alignment is always at least 1)
    /// ENSURES: return is a power of 2
    /// ENSURES: self.is_sized() implies return == self.layout.abi_align
    ///
    /// Note: We assume u64 and usize are the same since Kani is only supported in 64bits machines.
    #[cfg(target_pointer_width = "64")]
    pub fn align_of_head(&self) -> usize {
        if self.is_sized() {
            self.layout.abi_align.try_into().expect("alignment should fit")
        } else {
            match self.ty.kind().rigid().expect("should be monomorphized") {
                RigidTy::Slice(_) | RigidTy::Str | RigidTy::Dynamic(..) | RigidTy::Foreign(..) => 1,
                RigidTy::Adt(..) | RigidTy::Tuple(..) => {
                    let field_layout = self.last_field_layout();
                    field_layout
                        .align_of_head()
                        .max(self.layout.abi_align.try_into().expect("alignment should fit"))
                }
                _ => unreachable!("Expected sized type, but found: `{}`", self.ty), // external enum: FieldsShape
            }
        }
    }

    /// Return the size of the type if it's known at compilation time.
    pub fn size_of(&self) -> Option<usize> {
        if self.is_sized() { Some(self.layout.size.bytes()) } else { None }
    }

    /// Return the byte offset of a field within a struct or tuple.
    ///
    /// # Arguments
    /// * `field_idx` - The index of the field (0-based)
    ///
    /// # Returns
    /// The byte offset of the field from the start of the struct, or `None` if:
    /// - The type is not a struct/tuple
    /// - The field index is out of bounds
    /// - The layout doesn't have arbitrary field offsets
    ///
    /// REQUIRES: layout.fields is FieldsShape::Arbitrary to return Some
    /// ENSURES: Some(offset) iff field_idx exists in the offsets list
    pub fn field_offset(&self, field_idx: usize) -> Option<usize> {
        match &self.layout.fields {
            FieldsShape::Arbitrary { offsets } => offsets.get(field_idx).map(|off| off.bytes()),
            _ => None, // external enum: FieldsShape
        }
    }

    /// Byte offset of a field within an enum variant's layout (Part of #3527).
    pub fn variant_field_offset(&self, variant_idx: usize, field_idx: usize) -> Option<usize> {
        match &self.layout.variants {
            VariantsShape::Multiple { variants, .. } => {
                let vl = variants.get(variant_idx)?;
                if let FieldsShape::Arbitrary { offsets } = &vl.fields {
                    offsets.get(field_idx).map(|off| off.bytes())
                } else {
                    None
                }
            }
            VariantsShape::Single { .. } => self.field_offset(field_idx),
            _ => None, // external enum: VariantsShape
        }
    }

    /// Return the alignment of the type if it's known at compilation time.
    ///
    /// The alignment is known at compilation time for sized types and types with slice tail.
    ///
    /// Note: We assume u64 and usize are the same since Kani is only supported in 64bits machines.
    ///
    /// REQUIRES: self.ty has valid layout
    /// ENSURES: Some(align) implies align >= 1 and align is power of 2
    /// ENSURES: self.is_sized() implies Some(_)
    /// ENSURES: self.has_slice_tail() implies Some(_)
    #[cfg(target_pointer_width = "64")]
    pub fn align_of(&self) -> Option<usize> {
        if self.is_sized() || self.has_slice_tail() {
            self.layout.abi_align.try_into().ok()
        } else {
            None
        }
    }

    /// Test-only constructor that bypasses `ty.layout()`.
    #[cfg(test)]
    fn new_for_test(layout: LayoutShape) -> Self {
        // SAFETY: Ty is (usize, PhantomData<*const ()>). Zeroed memory is valid
        // for this repr and we never invoke methods on the dummy Ty in sized paths.
        let dummy_ty: Ty = unsafe { std::mem::zeroed() };
        LayoutOf { ty: dummy_ty, layout }
    }

    /// Return the layout of the last field of the type.
    ///
    /// REQUIRES: self.ty is Adt (struct/union, not enum) or Tuple
    /// REQUIRES: self.ty has at least one field
    /// ENSURES: return.ty is the type of the last field by offset order
    fn last_field_layout(&self) -> LayoutOf {
        match self.ty.kind().rigid().expect("should be monomorphized") {
            RigidTy::Adt(adt_def, adt_args) => {
                if adt_def.kind() == AdtKind::Enum {
                    unreachable!("Expected struct or tuple. Found enum: `{}`", self.ty);
                }
                let fields =
                    adt_def.variants_iter().next().expect("ADT should have variant").fields();
                let fields_sorted = self.layout.fields.fields_by_offset_order();
                let last_field_idx = *fields_sorted.last().expect("fields should not be empty");
                LayoutOf::new(fields[last_field_idx].ty_with_args(adt_args))
            }
            RigidTy::Tuple(tys) => {
                let fields_sorted = self.layout.fields.fields_by_offset_order();
                let last_field_idx = *fields_sorted.last().expect("fields should not be empty");
                let last_ty = tys[last_field_idx];
                LayoutOf::new(last_ty)
            }
            _ => unreachable!("Expected struct or tuple. Found: `{}`", self.ty), // external enum: RigidTy
        }
    }
}

/// Why [`LayoutOf::try_size_of_head`] could not measure the sized head of a type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HeadSizeError {
    /// The type is not rigid: it was not monomorphized.
    NotMonomorphized,
    /// The type is unsized but of a kind that carries no unsized tail.
    UnexpectedUnsizedKind,
    /// An unsized struct or tuple whose layout has no `FieldsShape::Arbitrary` offsets.
    NonArbitraryFields,
    /// An unsized struct or tuple whose layout lists no field to hold the unsized tail.
    NoFields,
    /// The tail field's offset plus the tail's head size does not fit in `usize`.
    Overflow,
}

impl std::fmt::Display for HeadSizeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            HeadSizeError::NotMonomorphized => "type should be monomorphized",
            HeadSizeError::UnexpectedUnsizedKind => "expected a type with an unsized tail",
            HeadSizeError::NonArbitraryFields => {
                "ADT and tuple types must have FieldsShape::Arbitrary layout"
            }
            HeadSizeError::NoFields => "fields should not be empty",
            HeadSizeError::Overflow => "head size overflows usize",
        })
    }
}

impl std::error::Error for HeadSizeError {}

/// Byte offset of the field that holds the unsized tail: the last field in offset order.
fn unsized_tail_offset(fields: &FieldsShape) -> Result<usize, HeadSizeError> {
    let FieldsShape::Arbitrary { offsets } = fields else {
        return Err(HeadSizeError::NonArbitraryFields);
    };
    let last = fields.fields_by_offset_order().last().copied().ok_or(HeadSizeError::NoFields)?;
    offsets.get(last).map(|offset| offset.bytes()).ok_or(HeadSizeError::NoFields)
}

/// Head size of an unsized aggregate: the tail field's offset plus the tail's own head size.
fn head_size_with_tail(tail_offset: usize, tail_head: usize) -> Result<usize, HeadSizeError> {
    tail_offset.checked_add(tail_head).ok_or(HeadSizeError::Overflow)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustc_public::abi::{FieldsShape, VariantsShape};
    use rustc_public::target::MachineSize;
    use rustc_public::ty::VariantIdx;
    use rustc_public_bridge::IndexedVal;

    // The two measured Trust endpoints (docs/DECISION_QUEUE.md, "Preserve both
    // native compiler API endpoints") name a layout's backend representation
    // differently: the 1.101 seal calls the enum `ValueRepr` and the field
    // `value_repr`, the 1.99 seal `ValueAbi` and `abi`. The variants these tests
    // build (`Scalar`, `Aggregate`) are the same on both.
    #[cfg(not(version("1.101")))]
    use rustc_public::abi::ValueAbi as ValueRepr;
    #[cfg(version("1.101"))]
    use rustc_public::abi::ValueRepr;

    /// Helper: a single-variant layout with the given fields, representation,
    /// alignment and size.
    #[cfg(version("1.101"))]
    fn single_variant_layout(
        fields: FieldsShape,
        value_repr: ValueRepr,
        abi_align: u64,
        size: MachineSize,
    ) -> LayoutShape {
        LayoutShape {
            fields,
            variants: VariantsShape::Single { index: VariantIdx::to_val(0) },
            value_repr,
            abi_align,
            size,
        }
    }

    #[cfg(not(version("1.101")))]
    fn single_variant_layout(
        fields: FieldsShape,
        value_repr: ValueRepr,
        abi_align: u64,
        size: MachineSize,
    ) -> LayoutShape {
        LayoutShape {
            fields,
            variants: VariantsShape::Single { index: VariantIdx::to_val(0) },
            abi: value_repr,
            abi_align,
            size,
        }
    }

    /// Helper: sized scalar layout (e.g. u32 = 32 bits, align 4)
    fn sized_scalar_layout(size_bytes: usize, align: u64) -> LayoutShape {
        single_variant_layout(
            FieldsShape::Primitive,
            ValueRepr::Scalar(rustc_public::abi::Scalar::Initialized {
                value: rustc_public::abi::Primitive::Int {
                    length: rustc_public::abi::IntegerLength::I32,
                    signed: false,
                },
                valid_range: rustc_public::abi::WrappingRange { start: 0, end: u32::MAX as u128 },
            }),
            align,
            MachineSize::from_bits(size_bytes * 8),
        )
    }

    /// Helper: sized aggregate layout (struct/tuple with field offsets)
    fn sized_struct_layout(
        offsets: Vec<usize>,
        total_size_bytes: usize,
        align: u64,
    ) -> LayoutShape {
        single_variant_layout(
            FieldsShape::Arbitrary {
                offsets: offsets.into_iter().map(|o| MachineSize::from_bits(o * 8)).collect(),
            },
            ValueRepr::Aggregate { sized: true },
            align,
            MachineSize::from_bits(total_size_bytes * 8),
        )
    }

    /// Helper: unsized aggregate layout
    fn unsized_aggregate_layout() -> LayoutShape {
        single_variant_layout(
            FieldsShape::Primitive,
            ValueRepr::Aggregate { sized: false },
            1,
            MachineSize::from_bits(0),
        )
    }

    #[test]
    fn test_sized_scalar_is_sized() {
        let layout = LayoutOf::new_for_test(sized_scalar_layout(4, 4));
        assert!(layout.is_sized());
    }

    #[test]
    fn test_unsized_aggregate_is_not_sized() {
        let layout = LayoutOf::new_for_test(unsized_aggregate_layout());
        assert!(!layout.is_sized());
    }

    #[test]
    fn test_sized_aggregate_is_sized() {
        let layout = LayoutOf::new_for_test(sized_struct_layout(vec![0, 4], 8, 4));
        assert!(layout.is_sized());
    }

    #[test]
    fn test_size_of_sized_scalar() {
        let layout = LayoutOf::new_for_test(sized_scalar_layout(4, 4));
        assert_eq!(layout.size_of(), Some(4));
    }

    #[test]
    fn test_size_of_sized_struct() {
        let layout = LayoutOf::new_for_test(sized_struct_layout(vec![0, 8], 16, 8));
        assert_eq!(layout.size_of(), Some(16));
    }

    #[test]
    fn test_size_of_unsized_returns_none() {
        let layout = LayoutOf::new_for_test(unsized_aggregate_layout());
        assert_eq!(layout.size_of(), None);
    }

    #[test]
    fn test_size_of_zero_sized() {
        let zst = single_variant_layout(
            FieldsShape::Primitive,
            ValueRepr::Aggregate { sized: true },
            1,
            MachineSize::from_bits(0),
        );
        let layout = LayoutOf::new_for_test(zst);
        assert_eq!(layout.size_of(), Some(0));
    }

    #[test]
    fn test_field_offset_first() {
        let layout = LayoutOf::new_for_test(sized_struct_layout(vec![0, 8, 16], 24, 8));
        assert_eq!(layout.field_offset(0), Some(0));
    }

    #[test]
    fn test_field_offset_middle() {
        let layout = LayoutOf::new_for_test(sized_struct_layout(vec![0, 8, 16], 24, 8));
        assert_eq!(layout.field_offset(1), Some(8));
    }

    #[test]
    fn test_field_offset_last() {
        let layout = LayoutOf::new_for_test(sized_struct_layout(vec![0, 8, 16], 24, 8));
        assert_eq!(layout.field_offset(2), Some(16));
    }

    #[test]
    fn test_field_offset_out_of_bounds() {
        let layout = LayoutOf::new_for_test(sized_struct_layout(vec![0, 8], 16, 8));
        assert_eq!(layout.field_offset(5), None);
    }

    #[test]
    fn test_field_offset_primitive_returns_none() {
        let layout = LayoutOf::new_for_test(sized_scalar_layout(4, 4));
        assert_eq!(layout.field_offset(0), None);
    }

    #[cfg(target_pointer_width = "64")]
    #[test]
    fn test_align_of_sized_returns_some() {
        let layout = LayoutOf::new_for_test(sized_scalar_layout(4, 4));
        assert_eq!(layout.align_of(), Some(4));
    }

    #[cfg(target_pointer_width = "64")]
    #[test]
    fn test_align_of_sized_8byte() {
        let layout = LayoutOf::new_for_test(sized_struct_layout(vec![0, 8], 16, 8));
        assert_eq!(layout.align_of(), Some(8));
    }

    #[test]
    fn test_size_of_head_sized() {
        let layout = LayoutOf::new_for_test(sized_scalar_layout(4, 4));
        assert_eq!(layout.size_of_head(), 4);
    }

    #[test]
    fn test_size_of_head_sized_struct() {
        let layout = LayoutOf::new_for_test(sized_struct_layout(vec![0, 4, 8], 12, 4));
        assert_eq!(layout.size_of_head(), 12);
    }

    #[test]
    fn test_try_size_of_head_sized_matches_size_of_head() {
        let layout = LayoutOf::new_for_test(sized_struct_layout(vec![0, 4, 8], 12, 4));
        assert_eq!(layout.try_size_of_head(), Ok(12));
    }

    /// Regression: the unsized head size was `offset + tail_head` unchecked, so a
    /// malformed layout wrapped silently in release builds instead of being reported.
    #[test]
    fn test_head_size_with_tail_reports_overflow() {
        assert_eq!(head_size_with_tail(usize::MAX, 1), Err(HeadSizeError::Overflow));
        assert_eq!(head_size_with_tail(1, usize::MAX), Err(HeadSizeError::Overflow));
        assert_eq!(head_size_with_tail(usize::MAX, 0), Ok(usize::MAX));
        assert_eq!(head_size_with_tail(16, 8), Ok(24));
    }

    #[test]
    fn test_unsized_tail_offset_is_last_field_by_offset() {
        let fields = FieldsShape::Arbitrary {
            offsets: [8usize, 0, 16, 4]
                .into_iter()
                .map(|o| MachineSize::from_bits(o * 8))
                .collect(),
        };
        assert_eq!(unsized_tail_offset(&fields), Ok(16));
    }

    /// Regression: a non-`Arbitrary` or empty field shape reached `unreachable!` / `expect`.
    #[test]
    fn test_unsized_tail_offset_rejects_malformed_fields() {
        assert_eq!(
            unsized_tail_offset(&FieldsShape::Primitive),
            Err(HeadSizeError::NonArbitraryFields)
        );
        assert_eq!(
            unsized_tail_offset(&FieldsShape::Arbitrary { offsets: Vec::new() }),
            Err(HeadSizeError::NoFields)
        );
    }

    #[cfg(target_pointer_width = "64")]
    #[test]
    fn test_align_of_head_sized() {
        let layout = LayoutOf::new_for_test(sized_scalar_layout(4, 4));
        assert_eq!(layout.align_of_head(), 4);
    }

    #[cfg(target_pointer_width = "64")]
    #[test]
    fn test_align_of_head_align_1() {
        let layout = LayoutOf::new_for_test(sized_scalar_layout(1, 1));
        assert_eq!(layout.align_of_head(), 1);
    }

    #[test]
    fn test_sized_has_no_foreign_tail() {
        let layout = LayoutOf::new_for_test(sized_scalar_layout(4, 4));
        assert!(!layout.has_foreign_tail());
    }

    #[test]
    fn test_sized_has_no_trait_tail() {
        let layout = LayoutOf::new_for_test(sized_scalar_layout(4, 4));
        assert!(!layout.has_trait_tail());
    }

    #[test]
    fn test_sized_has_no_slice_tail() {
        let layout = LayoutOf::new_for_test(sized_scalar_layout(4, 4));
        assert!(!layout.has_slice_tail());
    }

    #[test]
    fn test_sized_unsized_tail_is_none() {
        let layout = LayoutOf::new_for_test(sized_scalar_layout(4, 4));
        assert!(layout.unsized_tail().is_none());
    }

    #[test]
    fn test_sized_unsized_tail_elem_ty_is_none() {
        let layout = LayoutOf::new_for_test(sized_scalar_layout(4, 4));
        assert!(layout.unsized_tail_elem_ty().is_none());
    }

    #[test]
    fn test_field_offset_with_padding() {
        // Simulate struct { u8, /*3 padding*/, u32 } -> offsets [0, 4]
        let layout = LayoutOf::new_for_test(sized_struct_layout(vec![0, 4], 8, 4));
        assert_eq!(layout.field_offset(0), Some(0));
        assert_eq!(layout.field_offset(1), Some(4));
    }

    #[test]
    fn test_field_offset_union_returns_none() {
        let union_layout = single_variant_layout(
            FieldsShape::Union(std::num::NonZero::new(3).expect("non-zero")),
            ValueRepr::Aggregate { sized: true },
            4,
            MachineSize::from_bits(32),
        );
        let layout = LayoutOf::new_for_test(union_layout);
        assert_eq!(layout.field_offset(0), None);
    }

    #[test]
    fn test_field_offset_array_returns_none() {
        let array_layout = single_variant_layout(
            FieldsShape::Array { stride: MachineSize::from_bits(32), count: 10 },
            ValueRepr::Aggregate { sized: true },
            4,
            MachineSize::from_bits(320),
        );
        let layout = LayoutOf::new_for_test(array_layout);
        assert_eq!(layout.field_offset(0), None);
    }
}
