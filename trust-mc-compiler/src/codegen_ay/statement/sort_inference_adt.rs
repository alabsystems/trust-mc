// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! ADT sort inference for well-known Rust types.
//!
//! Extracted from sort_inference.rs (Part of #2246) to reduce file size.
//!
//! This module handles:
//! - `infer_wellknown_adt_from_ty` - Special-cased ADT type recognizers called
//!   from `infer_sort_from_ty`'s ADT branch
//! - `infer_adt_sort` - General ADT (enum/struct) sort inference

use crate::codegen_ay::names::{self, enum_sort, struct_sort};
use crate::codegen_ay::types::{bool_sort, bv8_sort, flatten_dt_array_element, int_sort, ptr_sort};
use ay_bindings::Sort;
use rustc_public::CrateDef;
use rustc_public::ty::{AdtDef, AdtKind, GenericArgKind, GenericArgs};

use super::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Handle well-known ADT types from `infer_sort_from_ty`'s ADT branch.
    ///
    /// Returns `Some(sort)` if the ADT is a recognized well-known type,
    /// `None` to fall through to general `infer_adt_sort`.
    #[must_use]
    pub(super) fn infer_wellknown_adt_from_ty(def: AdtDef, args: &GenericArgs) -> Option<Sort> {
        let adt_name = def.trimmed_name();

        // Transparent wrappers: unwrap to inner type
        if (adt_name == "MaybeUninit" || adt_name == "ManuallyDrop")
            && let Some(GenericArgKind::Type(inner_ty)) = args.0.first()
        {
            return Self::infer_sort_from_ty(*inner_ty);
        }

        // std::slice::Iter / IterMut have a dedicated simplified iterator model
        // (a `{fld_vec, fld_pos}` struct) that the iterator-next codegen
        // field-selects directly (e.g. collections/iter.rs). Since stage 1c's
        // `ty_with_args`, the generic struct path in `infer_adt_sort` can now
        // resolve their *real* fields (ptr / end_or_len / _marker) and would
        // declare THAT shape — disagreeing with the fld_vec/fld_pos selects and
        // producing an `unknown constant fld_vec` AY parse error that drops the
        // whole VC artifact (0 properties parsed → INCONCLUSIVE no-checks).
        // Model them with the simplified shape so declaration and use agree.
        if def.0.name().contains("slice::Iter")
            && args.0.iter().any(|a| matches!(a, GenericArgKind::Type(_)))
        {
            // Model `slice::Iter<'a, T>` IDENTICALLY to the runtime `.iter()`
            // codegen (collections/vec_view.rs): a SLICE-backed
            // `VecIter_Slice_<elem>` struct `{fld_vec: Slice_<elem>, fld_pos}`,
            // NOT a Vec-backed `Iter_lt_<T>`. `.iter()` on a slice produces a
            // Slice-backed value named `VecIter_<sort_short_name(slice)>`; ADT
            // sort inference must produce the SAME sort so that a struct field
            // of type `slice::Iter<T>` — e.g. `Copied<slice::Iter<T>>`'s
            // `fld_it` — is WELL-SORTED against the runtime iterator value.
            // (Previously the ADT model was `Iter_lt_<T>` Vec-backed with a
            // bv32 element — `vec_sort_from_args` read the LIFETIME as the first
            // generic arg — so `Copied::new(iter)` applied `Copied_mk` (field
            // `Iter_lt_PbLit`) to a `VecIter_Slice_bv40` value: an ILL-SORTED
            // constructor that made the base program spuriously UNSAT, hence a
            // vacuous verify. #g2-slice-iter-model-unification.) The Slice
            // datatype carries the same fld_len/fld_ptr/fld_data the
            // iterator-next codegen reads (collections/iter.rs), so the read
            // path is unchanged. Element sort read from the first TYPE arg
            // (skipping the lifetime) and flattened like the runtime data array.
            let elem_sort = args
                .0
                .iter()
                .find_map(|a| {
                    if let GenericArgKind::Type(t) = a {
                        Self::infer_sort_from_ty(*t)
                    } else {
                        None
                    }
                })
                .map(flatten_dt_array_element)
                .unwrap_or_else(|| Sort::bitvec(32));
            let slice_sort = Self::slice_sort(elem_sort);
            let name = {
                let short = names::sort_short_name(&slice_sort);
                let mut s = String::with_capacity(8 + short.len());
                s.push_str("VecIter_");
                s.push_str(&short);
                s
            };
            return Some(struct_sort(name, [("fld_vec", slice_sort), ("fld_pos", ptr_sort())]));
        }

        // #749: BigInt/BigUint types use Int sort for arbitrary precision.
        if adt_name == "BigInt" || adt_name == "BigUint" {
            return Some(int_sort());
        }
        // Ratio<BigInt> (BigRational) uses Int sort for simplification.
        if adt_name == "Ratio" {
            return Some(int_sort());
        }

        // NonNull/Unique: transparent pointer wrappers, model as raw pointer (bv64).
        // Part of #912: Generic type instantiation creates incompatible SMT sorts.
        if adt_name == "NonNull" || adt_name == "Unique" {
            return Some(ptr_sort());
        }

        // Part of #4067: Transparent data-extract wrappers. In single-threaded
        // verification, Mutex<T>/RwLock<T>/Cell<T>/UnsafeCell<T> are transparent
        // around T. ArcInner<T> is transparent around the data field (last generic
        // arg). Box/Rc/Arc are pointer wrappers (bv64). This mirrors the CHC
        // encoding in codegen_types_adt.rs and codegen_stmt_aggregate_wrapper.rs.
        if adt_name == "UnsafeCell" || adt_name == "Cell" {
            if let Some(GenericArgKind::Type(inner_ty)) = args.0.first() {
                return Self::infer_sort_from_ty(*inner_ty);
            }
        }
        if adt_name == "Mutex"
            || adt_name == "RwLock"
            || adt_name == "MutexGuard"
            || adt_name == "RwLockReadGuard"
            || adt_name == "RwLockWriteGuard"
            || adt_name == "ArcInner"
        {
            if let Some(GenericArgKind::Type(inner_ty)) = args.0.first() {
                return Self::infer_sort_from_ty(*inner_ty);
            }
        }
        // Box/Rc/Arc: pointer wrappers (bv64), consistent with CHC encoding.
        if adt_name == "Box" || adt_name == "Rc" || adt_name == "Arc" {
            return Some(ptr_sort());
        }
        // Part of #4067: Platform sync internals as scalar sorts. These types
        // contain pthread FFI fields that the BMC path cannot resolve. Encode
        // as fixed-width scalars, consistent with CHC codegen_types_adt.rs.
        let full_name = def.0.name();
        if full_name.contains("sys::sync::mutex")
            || full_name.contains("sys::pal::unix::sync")
            || full_name.contains("sync::poison::Flag")
        {
            return Some(Sort::bitvec(32));
        }
        if full_name.contains("once_box::OnceBox") || adt_name == "AtomicPtr" {
            return Some(ptr_sort());
        }

        // Part of #3159: DynMetadata<T> wraps a VTable pointer + PhantomData.
        // Encode as pointer-width bitvec, consistent with CHC encoding.
        if adt_name == "DynMetadata" {
            return Some(ptr_sort());
        }

        // Part of #3367: TypeId is a single-field wrapper around u128 (or two u64s).
        // Model as bv128 so Transmute(TypeId → u128) is identity and
        // Any::downcast_ref type equality checks are concrete.
        if adt_name == "TypeId" || adt_name == "std::any::TypeId" {
            return Some(Sort::bitvec(128));
        }

        // #1039: NonZero<T> is a transparent wrapper around T.
        if adt_name == "NonZero" {
            if let Some(GenericArgKind::Type(inner_ty)) = args.0.first()
                && let Some(inner_sort) = Self::infer_sort_from_ty(*inner_ty)
            {
                return Some(inner_sort);
            }
            return Some(ptr_sort());
        }

        // #967: IndexRange is a struct with two usize fields (start, end).
        if adt_name == "IndexRange" {
            return Some(names::index_range_sort());
        }

        // #967: PolymorphicIter<DATA> wraps IndexRange with a data pointer.
        if adt_name == "PolymorphicIter" {
            return Self::polymorphic_iter_sort(args);
        }

        // Part of #1811, #1835: IntoIter handling (Vec vs Array)
        if adt_name == "IntoIter" {
            return Self::into_iter_sort(def, args);
        }

        // Part of #1275, #1835: Vec<T>
        if adt_name == "Vec"
            || adt_name == "std::vec::Vec"
            || adt_name == "alloc::vec::Vec"
            || adt_name.ends_with("::Vec")
        {
            return Some(Self::vec_sort_from_args(args));
        }

        // Part of #1275: String
        if adt_name == "String" || adt_name == "std::string::String" {
            return Some(Self::string_sort());
        }

        // Part of #1275: RawVec<T, A>
        if adt_name == "RawVec" || adt_name == "alloc::raw_vec::RawVec" {
            return Some(Self::rawvec_sort());
        }

        // Part of #1275: Global allocator (zero-sized type)
        if adt_name == "Global" || adt_name == "std::alloc::Global" {
            return Some(bool_sort());
        }

        // #1524: Layout
        if adt_name == "Layout" || adt_name == "std::alloc::Layout" {
            return Some(Self::layout_sort());
        }

        // Part of #1622: Entry<K, V> enum for BTreeMap
        if adt_name == "Entry"
            || adt_name.ends_with("::Entry")
            || adt_name.contains("btree_map::Entry")
        {
            return Some(Self::btree_entry_sort());
        }

        // Part of #1622: VacantEntry<K, V>
        if adt_name == "VacantEntry"
            || adt_name.ends_with("::VacantEntry")
            || adt_name.contains("btree_map::VacantEntry")
        {
            return Some(Self::vacant_entry_sort());
        }

        // Part of #1622: OccupiedEntry<K, V>
        if adt_name == "OccupiedEntry"
            || adt_name.ends_with("::OccupiedEntry")
            || adt_name.contains("btree_map::OccupiedEntry")
        {
            return Some(Self::occupied_entry_sort());
        }

        // Part of #1622: SetValZST (BTreeSet value placeholder)
        if adt_name == "SetValZST"
            || adt_name.ends_with("::SetValZST")
            || adt_name.contains("set_val::SetValZST")
        {
            return Some(bool_sort());
        }

        None // Not a well-known type; fall through to infer_adt_sort
    }

    /// The sort a *sort-erased wrapper* was flattened to, when `Field` through it
    /// is the IDENTITY on the term.
    ///
    /// [`Self::infer_wellknown_adt_from_ty`] deliberately maps a family of
    /// single-payload wrappers — `ManuallyDrop<T>`, `MaybeUninit<T>`, `NonZero<T>`,
    /// and the interior-mutable `UnsafeCell<T>`/`Cell<T>`/`Mutex<T>` that the gate
    /// below then excludes — straight to the sort of the payload. The term for
    /// such a local is therefore the payload term, not a one-field datatype, and
    /// MIR's `Field(N)` through the wrapper (`ManuallyDrop::into_inner` is
    /// literally `slot.value`) has nothing to select: it must be the identity.
    /// Returns `Some(erased_sort)` exactly when all four hold for `base_ty`'s
    /// field `field_idx` of type `field_ty`:
    ///
    /// 1. `base_ty` is a `struct`/`union` ADT — single variant, so there is no
    ///    variant to get wrong;
    /// 2. it has exactly one non-ZST field and `field_idx` IS that field, so the
    ///    wrapper really is single-payload;
    /// 3. sort inference gives it a NON-datatype sort, i.e. it really was erased
    ///    (an ordinary `struct S(u8)` gets a datatype and is handled by the normal
    ///    field-select path, never here); and
    /// 4. the field being projected is represented by that SAME sort, i.e. it is
    ///    the slot the wrapper was erased to.
    ///
    /// (2) and (4) together are what keep a union honest. `MaybeUninit<u8>` erases
    /// to `bv8`; its field `value: ManuallyDrop<u8>` is its only non-ZST field and
    /// also erases to `bv8`, so it passes. Its `uninit: ()` is a ZST and is not the
    /// payload, so reading *that* field is refused. A user-written `union` is
    /// refused by (3): [`Self::infer_adt_sort`] gives `AdtKind::Union` no sort.
    ///
    /// # Not a width test
    ///
    /// Unlike `provenance::is_transparent_pointer_wrapper_repr` — which accepts any
    /// `bv64`, a plain `u64` included, and whose docs put widening it out of scope
    /// — this is TYPE-directed and re-derives the erasure decision from the MIR
    /// types. Pointer-width wrappers are deliberately EXCLUDED here so that
    /// `NonNull`/`Unique`/`Box` keep their existing, separately-documented
    /// treatment: this predicate answers only for the wrappers that previously
    /// fell through to a fail-closed.
    ///
    /// # One definition, both directions
    ///
    /// The read side (`apply_projection_chain`) uses it to make the projection the
    /// identity; the write side (`track_ref_pointees`) uses it to give
    /// `&mut (wrapper.N)` the wrapper's OWN ssa base name, because that borrow
    /// refers to the very same storage. If only one side knew, a write would land
    /// in a different slot than the read — the misalignment shape that fabricates
    /// proofs.
    #[must_use]
    pub(super) fn erased_wrapper_field_sort(
        base_ty: rustc_public::ty::Ty,
        field_idx: usize,
        field_ty: rustc_public::ty::Ty,
    ) -> Option<Sort> {
        let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, args)) =
            base_ty.kind()
        else {
            return None;
        };
        if !matches!(def.kind(), AdtKind::Struct | AdtKind::Union) {
            return None;
        }
        // The wrapper must be genuinely SINGLE-PAYLOAD, and `field_idx` must BE
        // that payload. Sort inference also models some MULTI-field ADTs as a
        // scalar — `BigInt { sign, data }` and `Ratio { numer, denom }` are each
        // one `Int` — and through those `Field` is emphatically not the identity:
        // reading `Ratio.numer` would hand back the whole ratio. Counting the
        // non-ZST fields is what separates "erased because it IS its payload"
        // from "modelled as a scalar".
        let mut payload = None;
        for (idx, f) in def.variants().first()?.fields().iter().enumerate() {
            if Self::layout_is_zst(f.ty_with_args(&args)) {
                continue;
            }
            if payload.is_some() {
                return None;
            }
            payload = Some(idx);
        }
        if payload != Some(field_idx) {
            return None;
        }
        let base_sort = Self::infer_sort_from_ty(base_ty)?;
        if base_sort.is_datatype()
            || crate::codegen_ay::provenance::is_transparent_pointer_wrapper_repr(&base_sort)
        {
            return None;
        }
        // INTERIOR MUTABILITY IS INCLUDED — this is the ONE STORAGE THEORY for a
        // `Cell`/`UnsafeCell` payload, and excluding it is what USED to fabricate
        // proofs, not what prevented them.
        //
        // The exclusion was written on the belief that `UnsafeCell::get` mints its
        // raw pointer on "a path that never goes through the borrow whose name
        // `track_ref_pointees` aligns". Measured on `Cell::new(7); c.set(9)`, that
        // is not what happens: `UnsafeCell::get` lowers to `&raw const (*self).0`,
        // i.e. exactly the Ref/AddressOf rvalue `track_ref_pointees` names. With
        // the exclusion in place the two sides of ONE location got two names —
        //
        //     write  `ptr::write(dest, 9)` -> env slot `<harness>::local_1_field_0`
        //     read   `Cell::get`           -> env slot `<harness>::local_1`
        //
        // — so `set` was invisible and `get()` returned the CONSTRUCTION value. The
        // exported VC for `c.set(9); assert!(c.get() == 7)` was UNSAT (i.e. would
        // be reported SUCCESSFUL); only AY's strict proof self-check downgrading it
        // to `unknown` kept that false PROOF off the console. Naming both sides
        // after the wrapper is what closes it: `assert!(c.get() == 7)` now FAILS
        // and `assert!(c.get() == 9)` SUCCEEDS.
        //
        // Two collaborators are REQUIRED for that to hold, both in `inline_body`:
        // the callee frame must carry the caller's SSA versions (else the write
        // re-defines `local_1_0` and the harness goes VACUOUS), and a write the
        // callee makes to caller-visible storage must propagate back to the
        // caller's env (else `Cell::get` still reads the pre-`set` value).
        if Self::infer_sort_from_ty(field_ty)? != base_sort {
            return None;
        }
        Some(base_sort)
    }

    /// Whether `ty` occupies no bytes. The same layout test `infer_adt_sort` uses
    /// to collapse a ZST struct, so the two agree; unlike `is_zst_type` it also
    /// sees `PhantomData` and other all-ZST composites. A type whose layout
    /// cannot be computed answers `false`, which only ever makes the caller
    /// refuse.
    pub(super) fn layout_is_zst(ty: rustc_public::ty::Ty) -> bool {
        ty.layout().ok().is_some_and(|l| l.shape().is_sized() && l.shape().size.bytes() == 0)
    }

    /// Infer AY sort for ADT (enum/struct) types.
    ///
    /// For unit enums (all variants have no fields), encodes as bitvector representing
    /// the discriminant. This avoids ay#517 (DT stub issue) by not using SMT datatypes.
    ///
    /// For Option-like enums (2 variants, one with 0 fields, one with 1 field), encodes
    /// as an SMT datatype with constructors for None and Some.
    ///
    /// Returns None for ADTs with fields that don't match supported patterns.
    #[must_use]
    pub(super) fn infer_adt_sort(def: AdtDef, args: GenericArgs) -> Option<Sort> {
        if let Some(sort) = Self::infer_wellknown_adt_from_ty(def, &args) {
            return Some(sort);
        }

        let variants = def.variants();
        let adt_name = Self::adt_sort_name(def, &args);

        // Check if this is a unit enum (all variants have no fields).
        // Only applies to actual enums — 0-field structs are ZSTs handled below.
        let is_unit_enum =
            def.kind() == AdtKind::Enum && variants.iter().all(|v| v.fields().is_empty());

        if is_unit_enum {
            // Bug fix (#1393): Use 32 bits as conservative default.
            let num_variants = variants.len();
            let bits = if num_variants <= 65536 { 32 } else { 64 };
            return Some(Sort::bitvec(bits));
        }

        // Check for Option-like enum: exactly 2 variants, one with 0 fields, one with 1 field
        if variants.len() == 2 {
            let v0_fields = variants[0].fields().len();
            let v1_fields = variants[1].fields().len();

            if (v0_fields == 0 && v1_fields == 1) || (v0_fields == 1 && v1_fields == 0) {
                let some_idx = if v0_fields > 0 { 0 } else { 1 };
                let some_variant = &variants[some_idx];

                if let Some(field) = some_variant.fields().first() {
                    let field_ty = field.ty();
                    let concrete_ty = Self::resolve_generic_ty(field_ty, &args);

                    if let Some(concrete_ty) = concrete_ty {
                        // #824 value-semantics: a Some payload that is a reference
                        // (`Option<&T>` / `Option<&mut T>` — e.g. `Iter/IterMut::next`
                        // returns `Option<&[mut] T>`) is constructed/produced as the
                        // DEREF'd value (get_option_payload_value derefs the ref;
                        // iter::next does `data.select(pos)`). The payload SORT must
                        // therefore be the pointee's value sort, NOT the bv64 pointer.
                        // Otherwise the declared Some-constructor arg (bv64) mismatches
                        // the value (e.g. bv32) and the emitted SMT is malformed —
                        // Z3 reports a sort error; AY silently returns reason-unknown
                        // incomplete (→ 0 properties parsed → false INCONCLUSIVE).
                        let payload_ty =
                            match concrete_ty.kind() {
                                rustc_public::ty::TyKind::RigidTy(
                                    rustc_public::ty::RigidTy::Ref(_, pointee, _),
                                ) => pointee,
                                _ => concrete_ty,
                            };
                        if let Some(payload_sort) = Self::infer_sort_from_ty(payload_ty) {
                            // Part of #2549: Use scoped constructor names to avoid
                            // Z3 "ambiguous function declaration" when multiple Option
                            // instantiations coexist (e.g., Option<i32> and Option<u32>).
                            return Some(enum_sort(
                                &adt_name,
                                names::option_constructors(&adt_name, payload_sort),
                            ));
                        }
                    }
                }
            }
        }

        // Handle structs: single variant with named fields
        if def.kind() == AdtKind::Struct {
            if variants.is_empty() {
                return None;
            }
            let variant = &variants[0];

            // Part of #3041 (extended): a struct that is a ZST encodes as Bool, matching
            // the convention for () (unit type). This now covers not only 0-field structs
            // but ALSO a 1+-field struct ALL of whose fields are ZSTs — e.g.
            // `pub struct TryFromIntError(())`, the `Err` payload of
            // `u16::try_from(x)`'s `Result<u16, TryFromIntError>`. The value side already
            // materializes a ZST as a bare Bool sentinel; without collapsing the SORT too,
            // the Err payload field is built as a struct datatype while its value is Bool
            // → a `Sort(Bool)` vs `Datatype(TryFromIntError)` mismatch (aggregate_adt) that
            // malforms the whole `Result_u16_..` datatype, so `Result::unwrap_or` can't
            // find its value field and the VC drops to INCONCLUSIVE (no checks). The layout
            // ZST test (size 0, sized) is the same predicate as chc::is_zst_ty.
            let is_zst_struct = variant.fields().is_empty()
                || rustc_public::ty::Ty::from_rigid_kind(rustc_public::ty::RigidTy::Adt(
                    def,
                    args.clone(),
                ))
                .layout()
                .ok()
                .is_some_and(|l| l.shape().is_sized() && l.shape().size.bytes() == 0);
            if is_zst_struct {
                return Some(bool_sort());
            }

            let mut fields = Vec::with_capacity(variant.fields().len());

            for field in variant.fields() {
                // Use rustc's real generic substitution. `resolve_generic_ty`
                // only substitutes a TOP-LEVEL `Param`, so a field whose type
                // NESTS a generic param — e.g. ArrayVec's `buf: [MaybeUninit<T>; N]`
                // — kept `T` unresolved, making `infer_sort_from_ty` fail and the
                // whole struct fall back to a default `bv32`. `ty_with_args`
                // substitutes recursively (matching the CHC path), so the field
                // becomes the concrete `[MaybeUninit<u32>; 4]` → `Array(bv64,bv32)`.
                let concrete_ty = field.ty_with_args(&args);
                let sort = Self::infer_sort_from_ty(concrete_ty)?;
                fields.push((names::adt_struct_field_name(&field.name), sort));
            }

            return Some(struct_sort(adt_name, fields));
        }

        // Handle general enums: multiple variants, each with any number of fields.
        // Part of #216: support for Result-like and general enums.
        if def.kind() == AdtKind::Enum {
            let mut constructors = Vec::with_capacity(variants.len());

            for variant in &variants {
                let mut fields = Vec::with_capacity(variant.fields().len());
                for (idx, field) in variant.fields().iter().enumerate() {
                    let field_ty = field.ty();
                    let concrete_ty = Self::resolve_generic_ty(field_ty, &args)?;
                    let sort = Self::infer_sort_from_ty(concrete_ty)?;
                    fields.push((names::variant_field_name(&variant.name(), idx), sort));
                }
                // Part of #2549: Scope Option constructor names.
                constructors.push((names::scope_option_ctor(variant.name(), &adt_name), fields));
            }

            return Some(enum_sort(adt_name, constructors));
        }

        None
    }

    // --- Sort construction helpers for well-known types ---

    /// PolymorphicIter<DATA> sort: struct { fld_alive: IndexRange, fld_data: DATA }
    #[must_use]
    fn polymorphic_iter_sort(args: &GenericArgs) -> Option<Sort> {
        if let Some(GenericArgKind::Type(data_ty)) = args.0.first()
            && let Some(data_sort) = Self::infer_sort_from_ty(*data_ty)
        {
            return Some(struct_sort(
                names::polymorphic_iter_sort_name(&names::sort_short_name(&data_sort)),
                [("fld_alive", names::index_range_sort()), ("fld_data", data_sort)],
            ));
        }
        // Fallback: just IndexRange if we can't resolve DATA
        Some(names::index_range_sort())
    }

    /// IntoIter sort: dispatches between Vec IntoIter and Array IntoIter.
    #[must_use]
    fn into_iter_sort(def: AdtDef, args: &GenericArgs) -> Option<Sort> {
        // Check if this is Vec's IntoIter by examining the full def path
        let full_name = def.0.name();
        let is_vec_into_iter = full_name.contains("vec::into_iter")
            || full_name.contains("vec::IntoIter")
            || full_name.contains("alloc::vec")
            || full_name.starts_with("alloc::vec")
            || full_name.contains("std::vec");

        if is_vec_into_iter {
            return Self::vec_into_iter_sort(args);
        }

        // #967: Array IntoIter<T, N> wraps PolymorphicIter<[MaybeUninit<T>; N]>.
        if let Some(GenericArgKind::Type(elem_ty)) = args.0.first()
            && let Some(elem_sort) = Self::infer_sort_from_ty(*elem_ty)
        {
            let array_sort = Sort::array(ptr_sort(), elem_sort.clone());
            return Some(struct_sort(
                names::into_iter_sort_name(&names::sort_short_name(&elem_sort)),
                [("fld_alive", names::index_range_sort()), ("fld_data", array_sort)],
            ));
        }
        // Fallback
        Some(names::index_range_sort())
    }

    /// Vec's IntoIter sort: 6-field struct matching MIR layout (Part of #2912).
    ///
    /// Rustc inlines `IntoIter::next()` which accesses all 6 fields of the real
    /// `std::vec::IntoIter<T>` struct. The BMC path must match this layout so
    /// field projections on indices 0-5 succeed.
    #[must_use]
    fn vec_into_iter_sort(args: &GenericArgs) -> Option<Sort> {
        if let Some(GenericArgKind::Type(elem_ty)) = args.0.first()
            && let Some(elem_sort) = Self::infer_sort_from_ty(*elem_ty)
        {
            // Part of #2267: Cow<str> auto-derefs to &str for name functions.
            let type_suffix = names::sort_short_name(&elem_sort);
            return Some(struct_sort(
                names::vec_into_iter_sort_name(&type_suffix),
                names::vec_into_iter_bmc_fields(),
            ));
        }
        // Fallback for Vec IntoIter with unknown element type
        Some(struct_sort("VecIntoIter_unknown", names::vec_into_iter_bmc_fields()))
    }

    /// Vec<T> sort from generic args.
    #[must_use]
    fn vec_sort_from_args(args: &GenericArgs) -> Sort {
        let elem_sort = args
            .0
            .first()
            .and_then(|arg| {
                if let GenericArgKind::Type(elem_ty) = arg {
                    Self::infer_sort_from_ty(*elem_ty)
                } else {
                    None
                }
            })
            .unwrap_or_else(|| Sort::bitvec(32));
        // Part of #2990: flatten DT elements to BV for PDR compatibility.
        let elem_sort = flatten_dt_array_element(elem_sort);
        let array_sort = Sort::array(ptr_sort(), elem_sort.clone());
        let type_suffix = names::sort_short_name(&elem_sort);
        struct_sort(names::vec_sort_name(&type_suffix), names::vec_fields(array_sort))
    }

    /// String sort: struct with (ptr, len, cap, data) where data is Array<usize, u8>.
    #[must_use]
    fn string_sort() -> Sort {
        let byte_array_sort = Sort::array(ptr_sort(), bv8_sort());
        struct_sort(names::RUST_STRING_SORT, names::vec_fields(byte_array_sort))
    }

    /// RawVec sort: struct with (ptr, cap).
    #[must_use]
    fn rawvec_sort() -> Sort {
        struct_sort("RawVec", names::rawvec_fields())
    }

    /// Layout sort: struct with (size, align).
    #[must_use]
    fn layout_sort() -> Sort {
        struct_sort("Layout", names::layout_fields())
    }

    /// BTreeMap Entry<K, V> enum sort.
    #[must_use]
    fn btree_entry_sort() -> Sort {
        enum_sort(
            "Entry",
            [
                (
                    "Vacant",
                    vec![(names::variant_field_name("Vacant", 0), Self::vacant_entry_sort())],
                ),
                (
                    "Occupied",
                    vec![(names::variant_field_name("Occupied", 0), Self::occupied_entry_sort())],
                ),
            ],
        )
    }

    /// VacantEntry<K, V> sort.
    #[must_use]
    fn vacant_entry_sort() -> Sort {
        struct_sort("VacantEntry", names::btree_entry_fields())
    }

    /// OccupiedEntry<K, V> sort.
    #[must_use]
    fn occupied_entry_sort() -> Sort {
        struct_sort("OccupiedEntry", names::btree_entry_fields())
    }
}
