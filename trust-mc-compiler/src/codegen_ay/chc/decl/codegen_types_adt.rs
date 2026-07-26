// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! ADT type-to-sort translation for CHC codegen.
//!
//! `translate_adt_ty`: ADT name-based sort dispatch (collections, pointer wrappers,
//! transparent wrappers, allocator infra, iterator types).
//! Extracted from include!() via extension trait. Part of #2306.

use ay_bindings::Sort;
use rustc_public::CrateDef;
use rustc_public::ty::{AdtDef, GenericArgKind, GenericArgs, RigidTy, TyKind};
use tracing::{debug, warn};

use crate::codegen_ay::types::{bool_sort, bv8_sort, flatten_dt_array_element, int_sort, ptr_sort};

use super::codegen_types::CodegenTypes;
use super::codegen_types_adt_sort::CodegenTypesAdtSort;
use super::names::{self, struct_sort};
use super::{ChcCtx, record_type_sort_fallback};

/// Extract the element sort T from PolymorphicIter<DATA> where DATA = [MaybeUninit<T>; N].
///
/// Unwraps Array → MaybeUninit to reach the inner element type T, then translates it.
/// Falls back to bv8 if any step fails (unresolvable generic, unexpected structure).
/// Part of #3984: mirrors the IntoIter handler's element extraction logic.
fn extract_polymorphic_iter_elem(args: &GenericArgs) -> Sort {
    // PolymorphicIter has one type arg: DATA.
    let data_arg = args
        .0
        .iter()
        .find_map(|arg| if let GenericArgKind::Type(ty) = arg { Some(ty) } else { None });
    let Some(data_ty) = data_arg else {
        record_type_sort_fallback("PolymorphicIter data sort (no type arg)");
        return bv8_sort();
    };
    // DATA should be [MaybeUninit<T>; N] — an Array type.
    let elem_ty = match data_ty.kind() {
        TyKind::RigidTy(RigidTy::Array(array_elem, _)) => array_elem,
        _ => {
            // DATA is not an array — try translating directly as the element.
            return ChcCtx::translate_type_arg_sort_or_param_bv(
                Some(&GenericArgKind::Type(*data_ty)),
                "PolymorphicIter element sort",
                bv8_sort(),
            );
        }
    };
    // array_elem should be MaybeUninit<T> — unwrap to get T.
    let inner_ty = match elem_ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, mu_args))
            if def.trimmed_name() == "MaybeUninit"
                || def.trimmed_name() == "std::mem::MaybeUninit" =>
        {
            mu_args
                .0
                .iter()
                .find_map(|a| if let GenericArgKind::Type(ty) = a { Some(*ty) } else { None })
        }
        _ => None,
    };
    let target_ty = inner_ty.unwrap_or(elem_ty);
    ChcCtx::translate_type_arg_sort_or_param_bv(
        Some(&GenericArgKind::Type(target_ty)),
        "PolymorphicIter element sort",
        bv8_sort(),
    )
}

/// Extension trait for ADT name-based sort dispatch on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CodegenTypesAdt<'tcx, 'body> {
    fn nth_type_arg(args: &GenericArgs, idx: usize) -> Option<&GenericArgKind>;
    fn translate_type_arg_sort_or_param_bv(
        arg: Option<&GenericArgKind>,
        fallback_site: &'static str,
        fallback_sort: Sort,
    ) -> Sort;
    #[must_use]
    fn translate_adt_ty(def: AdtDef, args: GenericArgs) -> Option<Sort>;
}

impl<'tcx, 'body> CodegenTypesAdt<'tcx, 'body> for ChcCtx<'tcx, 'body> {
    /// Return the nth type generic argument, skipping const/lifetime args.
    fn nth_type_arg(args: &GenericArgs, idx: usize) -> Option<&GenericArgKind> {
        args.0.iter().filter(|arg| matches!(arg, GenericArgKind::Type(_))).nth(idx)
    }

    /// Translate a generic type argument to a sort with a generic-param-aware fallback.
    ///
    /// For unresolved type parameters (`TyKind::Param`), prefer pointer-width
    /// bitvectors over hard-coded fallback sorts so iterator/collection key sorts
    /// remain shape-compatible in non-monomorphized std MIR.
    fn translate_type_arg_sort_or_param_bv(
        arg: Option<&GenericArgKind>,
        fallback_site: &'static str,
        fallback_sort: Sort,
    ) -> Sort {
        if let Some(GenericArgKind::Type(ty)) = arg {
            if let Some(sort) = Self::translate_ty(*ty) {
                return sort;
            }
            if matches!(ty.kind(), TyKind::Param(_)) {
                return ptr_sort();
            }
        }
        record_type_sort_fallback(fallback_site);
        fallback_sort
    }

    /// Translates an ADT (struct/enum) type to a AY sort by name-based dispatch.
    ///
    /// Handles collections, pointer wrappers, transparent wrappers, allocator
    /// infrastructure, iterator types, and falls through to field-based translation.
    fn translate_adt_ty(def: AdtDef, args: GenericArgs) -> Option<Sort> {
        let name = def.trimmed_name();
        debug!(adt_name = ?name, "matched ADT arm");

        // BigRational/Ratio → SMT Real (#911, #3814: exact match only)
        if name == "BigRational" || name == "Ratio" {
            return Some(Sort::real());
        }
        // BigInt/BigUint → SMT Int (#734, #3814: exact match only)
        if name == "BigInt" || name == "BigUint" {
            return Some(int_sort());
        }
        // HashMap/BTreeMap/TrustMcMap → Array<K,V> (#788, #3057: parallel-array encoding)
        if name == "HashMap" || name == "BTreeMap" || name == "TrustMcMap" {
            let key_sort = Self::translate_type_arg_sort_or_param_bv(
                args.0.first(),
                "HashMap/BTreeMap key sort",
                int_sort(),
            );

            let val_sort = Self::translate_type_arg_sort_or_param_bv(
                Self::nth_type_arg(&args, 1),
                "HashMap/BTreeMap value sort",
                int_sort(),
            );

            debug!(?key_sort, ?val_sort, "HashMap translated to DT-free Array (#3057)");
            return Some(Sort::array(key_sort, val_sort));
        }

        // HashSet/BTreeSet → Array<K, Bool> (#1751)
        if name == "HashSet" || name == "BTreeSet" {
            let key_sort = Self::translate_type_arg_sort_or_param_bv(
                args.0.first(),
                "HashSet/BTreeSet key sort",
                int_sort(),
            );

            debug!(?key_sort, adt_name = ?name, "Set translated to Array<K, Bool>");
            return Some(Sort::array(key_sort, bool_sort()));
        }

        // NonNull/Unique: transparent pointer wrappers (Part of #912)
        if name == "NonNull" || name == "Unique" {
            debug!(adt_name = ?name, "pointer wrapper type -> bv64 sort");
            return Some(ptr_sort());
        }

        // Part of #4251: Rc/Arc/Weak — reference-counted pointer wrappers.
        // These are heap pointers like Box; encode as ptr_sort() (BV64).
        // Without this, translate_adt_sort attempts field-by-field translation
        // which fails on internal RcInner/ArcInner fields, returning None and
        // cascading into bv32 fallback at state var declaration.
        // Matches BMC encoder: sort_inference_adt.rs line 75.
        if name == "Rc"
            || name == "Arc"
            || name == "Weak"
            || name == "std::rc::Rc"
            || name == "std::sync::Arc"
            || name == "std::rc::Weak"
            || name == "std::sync::Weak"
        {
            debug!(adt_name = ?name, "Rc/Arc/Weak -> bv64 sort (pointer wrapper)");
            return Some(ptr_sort());
        }

        // Part of #4251: RcInner — Rc's internal allocation struct.
        // Contains strong/weak counts + data. Model as opaque pointer since
        // Rc<T> is already modeled as ptr_sort() and internal fields are not
        // directly accessed in verification.
        if name == "RcInner" || name == "alloc::rc::RcInner" {
            debug!(adt_name = ?name, "RcInner -> bv64 sort (opaque)");
            return Some(ptr_sort());
        }

        // Part of #3159: DynMetadata<T> wraps a VTable pointer + PhantomData.
        // Encode as pointer-width bitvec to match fat-pointer metadata expectations.
        // Without this, DynMetadata is translated as a Datatype which causes
        // sort mismatches when assigned to BV64 locals in pointer metadata ops.
        if name == "DynMetadata" {
            debug!(adt_name = ?name, "DynMetadata -> bv64 sort (vtable pointer)");
            return Some(ptr_sort());
        }

        // #1166: String type
        if name == "String" || name == "std::string::String" {
            debug!(adt_name = ?name, "String -> Datatype sort (ptr, len, cap)");
            return Some(struct_sort(names::RUST_STRING_SORT, names::string_fields()));
        }

        // #1166, #1632, #1835: Vec<T>
        if name == "Vec"
            || name == "std::vec::Vec"
            || name == "alloc::vec::Vec"
            || name.ends_with("::Vec")
        {
            let elem_sort = Self::translate_type_arg_sort_or_param_bv(
                args.0.first(),
                "Vec element sort",
                ptr_sort(),
            );
            // Part of #2990: flatten DT elements to BV for PDR compatibility,
            // matching Array/Slice flattening in translate_ty.
            let elem_sort = flatten_dt_array_element(elem_sort);
            // Part of #2267: Cow<str> auto-derefs to &str for name functions.
            let type_suffix = names::sort_short_name(&elem_sort);
            let array_sort = Sort::array(ptr_sort(), elem_sort);
            debug!(adt_name = ?name, type_suffix = %type_suffix, "Vec -> Datatype sort (ptr, len, cap, data)");
            return Some(struct_sort(
                names::vec_sort_name(&type_suffix),
                names::vec_fields(array_sort),
            ));
        }

        // Part of #4251: VecDeque<T> — ring buffer, model as Vec<T> equivalent.
        // VecDeque's internal layout (head, len, buf: RawVec<T>) would fail
        // field-by-field translation when T is unresolvable, cascading to bv32.
        // Use the same (ptr, len, cap, data) layout as Vec<T>.
        if name == "VecDeque"
            || name == "std::collections::VecDeque"
            || name.ends_with("::VecDeque")
        {
            let elem_sort = Self::translate_type_arg_sort_or_param_bv(
                args.0.first(),
                "VecDeque element sort",
                ptr_sort(),
            );
            let elem_sort = flatten_dt_array_element(elem_sort);
            let type_suffix = names::sort_short_name(&elem_sort);
            let array_sort = Sort::array(ptr_sort(), elem_sort);
            debug!(adt_name = ?name, type_suffix = %type_suffix, "VecDeque -> Vec-like Datatype sort");
            return Some(struct_sort(
                format!("VecDeque_{type_suffix}"),
                names::vec_fields(array_sort),
            ));
        }

        // #1166: Box<T>
        if name == "Box" || name == "std::boxed::Box" {
            debug!(adt_name = ?name, "Box -> bv64 sort (pointer)");
            return Some(ptr_sort());
        }

        // Part of #3099: Cow<'_, B> — borrow-or-own wrapper.
        // Cow's Owned variant field type is an associated type projection
        // (<B as ToOwned>::Owned) which translate_adt_sort cannot resolve.
        // Model as pointer-sized bitvec, consistent with Box/NonNull.
        if name == "Cow" && !args.0.is_empty() {
            debug!(adt_name = ?name, "Cow -> bv64 sort (pointer-like wrapper)");
            return Some(ptr_sort());
        }

        // #1166: RawVec<T, A>
        if name == "RawVec" || name == "alloc::raw_vec::RawVec" {
            debug!(adt_name = ?name, "RawVec -> Datatype sort (ptr, cap)");
            return Some(struct_sort("RawVec", names::rawvec_fields()));
        }

        // #1166: Global allocator
        if name == "Global" || name == "std::alloc::Global" {
            debug!(adt_name = ?name, "Global allocator -> Bool (ZST)");
            return Some(bool_sort());
        }

        // Transparent wrappers: delegate to inner type
        // Transparent single-field wrappers: delegate to inner T.
        // Includes mem wrappers, cell wrappers, and (#4067) sync wrappers + ArcInner.
        // Sync wrappers gated on non-empty args to exclude internal platform types.
        let is_transparent_wrapper = matches!(
            name.as_str(),
            "ManuallyDrop"
                | "std::mem::ManuallyDrop"
                | "MaybeUninit"
                | "std::mem::MaybeUninit"
                | "UnsafeCell"
                | "std::cell::UnsafeCell"
                | "Cell"
                | "std::cell::Cell"
        ) || (!args.0.is_empty()
            && matches!(
                name.as_str(),
                "Mutex"
                    | "std::sync::Mutex"
                    | "RwLock"
                    | "std::sync::RwLock"
                    | "MutexGuard"
                    | "std::sync::MutexGuard"
                    | "RwLockReadGuard"
                    | "std::sync::RwLockReadGuard"
                    | "RwLockWriteGuard"
                    | "std::sync::RwLockWriteGuard"
                    | "PoisonError"
                    | "std::sync::PoisonError"
                    | "ArcInner"
                    | "alloc::sync::ArcInner"
            ));
        if is_transparent_wrapper {
            if let Some(GenericArgKind::Type(inner_ty)) = args.0.first() {
                return Self::translate_ty(*inner_ty);
            }
        }
        // Part of #4251: Ref/RefMut — borrow guards from RefCell.
        // Use full path to avoid matching other types named "Ref".
        // These wrap a reference to the inner T; model as transparent around T.
        // Without this, field-by-field translation fails on the BorrowRef/BorrowRefMut
        // internal fields, cascading into bv32 fallback.
        // Part of #4067: Platform sync types as transparent scalars.
        // Use def.0.name() (full path) since trimmed_name() strips module prefix.
        let full_name = def.0.name();
        if (name == "Ref" || name == "RefMut") && full_name.contains("cell") {
            if let Some(GenericArgKind::Type(inner_ty)) = args.0.first() {
                debug!(adt_name = ?name, "cell::Ref/RefMut -> delegate to inner type");
                return Self::translate_ty(*inner_ty);
            }
        }
        if full_name.contains("sys::sync::mutex")
            || full_name.contains("sys::pal::unix::sync")
            || full_name.contains("sync::poison::Flag")
        {
            return Some(Sort::bitvec(32));
        }
        if full_name.contains("once_box::OnceBox")
            || name == "AtomicPtr"
            || name == "std::sync::atomic::AtomicPtr"
        {
            return Some(ptr_sort());
        }
        if name == "NonZero" || name == "std::num::NonZero" || name.ends_with("::NonZero") {
            if let Some(GenericArgKind::Type(inner_ty)) = args.0.first() {
                debug!(adt_name = ?name, "NonZero -> delegate to inner type");
                return Self::translate_ty(*inner_ty);
            }
            warn!(adt_name = ?name, "NonZero without generic type arg");
        }

        // Part of #3792, #4086: Single-field array wrapper transparent unwrapping.
        // Structs wrapping a single [T; N] field (including #[repr(simd)] types
        // like i64x2([i64; 2]) and std::simd::Simd<T, N>) delegate to the inner
        // array sort. This avoids a Datatype wrapper that causes sort mismatches
        // in transmute (identity cast), comparison dispatch, and SIMD intrinsics.
        // Previously gated on name.contains("simd") which missed user-defined
        // #[repr(simd)] types like `i64x2` — the structural check (1 variant,
        // 1 field, field is [T; N]) is sufficient.
        if def.variants().len() == 1 && def.variants()[0].fields().len() == 1 {
            let field_ty = def.variants()[0].fields()[0].ty_with_args(&args);
            if matches!(field_ty.kind(), TyKind::RigidTy(RigidTy::Array(..))) {
                debug!(adt_name = ?name, "single-field array wrapper -> delegate to inner array type");
                return Self::translate_ty(field_ty);
            }
        }

        // #1979: Allocator infrastructure types — flatten to bitvectors
        if name == "Layout" || name == "Arguments" {
            debug!(adt_name = ?name, "alloc/fmt infra -> bv128 (opaque)");
            return Some(Sort::bitvec(128));
        }
        if name == "Alignment" {
            return Some(ptr_sort());
        }
        if name == "AllocError" || name == "Infallible" {
            return Some(bool_sort());
        }
        // #3521: ControlFlow falls through to translate_adt_sort general enum path.
        // #3367: TypeId wraps u128 (type identity for Any::downcast_ref).
        if name == "TypeId" || name == "std::any::TypeId" {
            debug!(adt_name = ?name, "any::TypeId -> bv128 (opaque)");
            return Some(Sort::bitvec(128));
        }

        // #4117: str::pattern internals + PhantomData → Bool (opaque ZST)
        if is_bool_adt_name(&name, &full_name, &args) {
            return Some(bool_sort());
        }
        // #4112 FlatMap/FlattenCompat, #4160 Chain/Fuse — opaque iterator adapters.
        // Part of #4251: Enumerate/Zip/Map/Rev/Skip/Take/Peekable/StepBy/FilterMap
        // — additional opaque iterator adapters. These contain complex internal
        // fields (closures, source iterators) that fail field-by-field translation.
        // Model as ptr_sort() (opaque pointer) since the verification stubs handle
        // iterator semantics at the call level, not the type level.
        if matches!(
            name.as_str(),
            "FlatMap"
                | "FlattenCompat"
                | "Chain"
                | "Fuse"
                | "Enumerate"
                | "Zip"
                | "Rev"
                | "Skip"
                | "Take"
                | "Peekable"
                | "StepBy"
                | "FilterMap"
                | "TakeWhile"
                | "SkipWhile"
                | "Inspect"
                | "Scan"
                | "Cloned"
                | "Copied"
        ) && (full_name.contains("iter") || full_name.contains("slice"))
        {
            debug!(adt_name = ?name, "iterator adapter -> bv64 (opaque)");
            return Some(ptr_sort());
        }
        // Part of #4251: Map — only when it's an iterator adapter (core::iter::adapters::Map),
        // not std::collections maps. Disambiguate via full path.
        if name == "Map" && full_name.contains("iter") {
            debug!(adt_name = ?name, "iter::Map adapter -> bv64 (opaque)");
            return Some(ptr_sort());
        }
        // Part of #4251: Filter — only when it's an iterator adapter, not str::pattern::Filter.
        if name == "Filter" && full_name.contains("iter::adapters") {
            debug!(adt_name = ?name, "iter::Filter adapter -> bv64 (opaque)");
            return Some(ptr_sort());
        }
        // Part of #4251: Drain — collection drain iterator. Contains internal
        // pointers and references that fail field-by-field translation.
        // Model as opaque pointer since drain semantics are handled at call level.
        if name == "Drain" {
            debug!(adt_name = ?name, "Drain -> bv64 (opaque iterator)");
            return Some(ptr_sort());
        }
        // Part of #4251: BTreeMap Entry/VacantEntry/OccupiedEntry types.
        // These contain internal tree node pointers that fail field-by-field translation.
        // Model as opaque pointers, consistent with BMC encoder (sort_inference_adt.rs).
        // The Entry enum is 2-variant (Occupied/Vacant) but fields contain tree internals.
        if (name == "Entry"
            || name == "VacantEntry"
            || name == "OccupiedEntry"
            || name.ends_with("::Entry")
            || name.ends_with("::VacantEntry")
            || name.ends_with("::OccupiedEntry"))
            && (full_name.contains("btree_map") || full_name.contains("hash_map"))
        {
            debug!(adt_name = ?name, "map Entry -> bv64 (opaque)");
            return Some(ptr_sort());
        }
        if name == "SetValZST"
            || name.ends_with("::SetValZST")
            || name.contains("set_val::SetValZST")
        {
            debug!(adt_name = ?name, "SetValZST -> Bool (ZST)");
            return Some(bool_sort());
        }
        if name == "IndexRange" {
            debug!(adt_name = ?name, "IndexRange -> Datatype sort");
            return Some(names::index_range_sort());
        }
        if name == "PolymorphicIter" || name.ends_with("::PolymorphicIter") {
            debug!(adt_name = ?name, "PolymorphicIter -> Datatype sort");
            // #3984: extract elem T from DATA=[MaybeUninit<T>; N], flatten to Array.
            let elem_sort = extract_polymorphic_iter_elem(&args);
            let elem_sort = flatten_dt_array_element(elem_sort);
            let data_sort = Sort::array(ptr_sort(), elem_sort);
            return Some(struct_sort(
                "PolymorphicIter",
                [("fld_alive", names::index_range_sort()), ("fld_data", data_sort)],
            ));
        }

        // Iterator types
        //
        // RawIntoIter is hashbrown's internal raw iterator used by both HashMap
        // and HashSet. Discriminate by type parameter shape:
        //   RawIntoIter<(K, V)> → HashMap (tuple element = key-value pair)
        //   RawIntoIter<K>      → HashSet (non-tuple element = key only)
        if name == "RawIntoIter" || name == "hashbrown::raw::RawIntoIter" {
            // Check if the type parameter is a 2-element tuple (HashMap case)
            if let Some(GenericArgKind::Type(ty)) = args.0.first()
                && let TyKind::RigidTy(RigidTy::Tuple(tys)) = ty.kind()
                && tys.len() == 2
            {
                debug!(adt_name = ?name, "RawIntoIter<(K,V)> -> HashMapIntoIter sort");
                let k_sort = Self::translate_ty(tys[0]).unwrap_or_else(|| {
                    record_type_sort_fallback("RawIntoIter HashMap key sort");
                    ptr_sort()
                });
                let v_sort = Self::translate_ty(tys[1]).unwrap_or_else(|| {
                    record_type_sort_fallback("RawIntoIter HashMap value sort");
                    ptr_sort()
                });
                // Part of #2267: Cow<str> auto-derefs to &str for name functions.
                let key_suffix = names::sort_short_name(&k_sort);
                let val_suffix = names::sort_short_name(&v_sort);

                // Part of #3057: DT-free parallel-array encoding.
                // data: Array(K, V), present: Array(K, Bool) — no Option DT.
                let data_sort = Sort::array(k_sort.clone(), v_sort);
                let present_sort = Sort::array(k_sort.clone(), bool_sort());
                let keys_sort = Sort::array(ptr_sort(), k_sort);

                return Some(struct_sort(
                    names::hashmap_into_iter_sort_name(&key_suffix, &val_suffix),
                    names::hashmap_iter_fields(data_sort, present_sort, keys_sort),
                ));
            }

            // Non-tuple type parameter: HashSet iterator
            debug!(adt_name = ?name, "RawIntoIter<K> -> HashSetIntoIter sort");
            let key_sort = Self::translate_type_arg_sort_or_param_bv(
                args.0.first(),
                "RawIntoIter key sort",
                ptr_sort(),
            );
            // Part of #2267: Cow<str> auto-derefs to &str for name functions.
            let type_suffix = names::sort_short_name(&key_sort);
            let set_sort = Sort::array(key_sort.clone(), bool_sort());
            let keys_sort = Sort::array(ptr_sort(), key_sort);

            return Some(struct_sort(
                names::hashset_into_iter_sort_name(&type_suffix),
                names::hashset_iter_fields(set_sort, keys_sort),
            ));
        }

        if name == "IntoIter"
            && let Some(sort) = Self::translate_into_iter_sort(def, &args)
        {
            return Some(sort);
        }

        // #3012: slice::Iter<'a, T> and slice::IterMut<'a, T> — produce SliceIter sort
        // with (fld_vec: Slice_<elem>, fld_pos: bv64) layout matching what
        // make_vec_into_iter_chc produces from a Slice input. Without this,
        // translate_adt_sort produces a generic sort that classify_collection_projection
        // misclassifies as VecIntoIter, causing reconstruction failure at stub sites.
        if (name == "Iter" || name == "IterMut") && def.0.name().contains("slice") {
            let elem_sort = Self::translate_type_arg_sort_or_param_bv(
                Self::nth_type_arg(&args, 0),
                "slice::Iter element sort",
                ptr_sort(),
            );
            // Part of #2990: flatten DT elements to BV for PDR compatibility.
            let elem_sort = flatten_dt_array_element(elem_sort);
            // Part of #2267: Cow<str> auto-derefs to &str for name functions.
            let type_suffix = names::sort_short_name(&elem_sort);
            let data_sort = Sort::array(ptr_sort(), elem_sort);
            let slice_sort = struct_sort(
                names::slice_sort_name(&type_suffix),
                [("fld_ptr", ptr_sort()), ("fld_len", ptr_sort()), ("fld_data", data_sort)],
            );
            debug!(
                adt_name = ?name, type_suffix = %type_suffix,
                "slice::Iter -> SliceIter sort (#3012)"
            );
            return Some(struct_sort(
                {
                    let mut s = String::with_capacity(10 + type_suffix.len());
                    s.push_str("SliceIter_");
                    s.push_str(&type_suffix);
                    s
                },
                names::vec_into_iter_fields(slice_sort),
            ));
        }

        // Part of #3945: hashbrown internal types (Bucket, RawTable, RawTableInner,
        // Group, etc.) are abstracted away by the HashMap stub system. If they leak
        // through drop glue or inline fallback, translating them as Datatype sorts
        // creates undeclared sorts in the CHC output (the sort appears in rule body
        // expressions but is never in state variables). Map to ptr_sort(), consistent
        // with memory_type_key_tables.rs which treats hashbrown_raw_Bucket_* as
        // pointer-width values.
        if Self::is_hashbrown_internal(def) {
            debug!(
                adt_name = ?name, full_path = ?def.0.name(),
                "hashbrown internal type -> bv64 (opaque pointer) (#3945)"
            );
            return Some(ptr_sort());
        }

        // #1979: Last-resort flattening for allocator/fmt infrastructure ADTs
        if Self::is_opaque_alloc_infra(def) {
            debug!(
                adt_name = ?name, full_path = ?def.0.name(),
                "allocator/fmt infrastructure ADT -> bv128 (opaque)"
            );
            return Some(Sort::bitvec(128));
        }

        // #1979: Flatten generic wrappers containing allocator infrastructure types.
        // `Infallible` is EXCLUDED from the wrapper-arg check: blobifying
        // `Result<Infallible, E>` (the `?`-operator residual, e.g. Enum/niche.rs)
        // to an opaque bv128 makes every enum construct/project/discriminant on
        // it fall into FailClose gap lanes and taint an otherwise-proven harness.
        // The general enum datatype path handles Infallible fields precisely
        // (uninhabited -> Bool), so the wrapper needs no blob for it.
        let has_alloc_infra_arg = args.0.iter().any(|arg| {
            if let GenericArgKind::Type(ty) = arg
                && let TyKind::RigidTy(RigidTy::Adt(inner_def, _)) = ty.kind()
            {
                return Self::is_opaque_alloc_infra(inner_def)
                    && inner_def.trimmed_name() != "Infallible";
            }
            false
        });
        if has_alloc_infra_arg {
            debug!(
                adt_name = ?name,
                "generic wrapper with alloc infra type arg -> bv128 (opaque)"
            );
            return Some(Sort::bitvec(128));
        }

        Self::translate_adt_sort(def, args)
    }
}

/// #4117: str::pattern internals + PhantomData are opaque Bool (ZST).
fn is_bool_adt_name(n: &str, full: &str, args: &GenericArgs) -> bool {
    matches!(
        n,
        "IsWhitespace"
            | "IsNotEmpty"
            | "SplitWhitespace"
            | "SplitInternal"
            | "CharPredicateSearcher"
            | "PhantomData"
            | "std::marker::PhantomData"
    ) || (n == "Split" && full.contains("str"))
        || (n == "Filter" && format!("{args:?}").contains("IsWhitespace"))
}
