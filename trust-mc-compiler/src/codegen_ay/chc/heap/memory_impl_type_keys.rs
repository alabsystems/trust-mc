// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//! Type key/sort mapping for CHC abstract heap model.
//! Converted from include!() to proper module per #2595.
use super::codegen_types::CodegenTypes;
use super::memory_impl_layout::unwrap_heap_transparent_ty;
use super::types::{bool_sort, bv8_sort, ptr_sort};
use super::{ChcCtx, record_type_sort_fallback};
use ay_bindings::Sort;
use rustc_middle::ty::TypingEnv;
use rustc_public::CrateDef;
use rustc_public::rustc_internal;
use rustc_public::ty::{FloatTy, GenericArgKind, IntTy, RigidTy, TyKind, UintTy};
use std::borrow::Cow;
use tracing::{debug, warn};
impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    // ============================================================================
    // Type Key / Sort Mapping
    // ============================================================================
    /// Conservative fallback sort for unknown type keys.
    ///
    /// We model unknown values as an opaque byte-addressed blob instead of an
    /// arbitrary scalar bit-width. This avoids unsound scalar truncation when
    /// the real type width is unknown (#2315).
    #[must_use]
    pub(in crate::codegen_ay::chc) fn unknown_type_key_fallback_sort() -> Sort {
        Sort::array(ptr_sort(), bv8_sort())
    }
    /// Computes total bit-width from a Datatype sort's constructor fields.
    /// Returns `Some(total_bits)` when every field is bitvec/bool/nested Datatype;
    /// `None` if any leaf has a non-scalar sort. Sums raw field widths without
    /// padding. Part of #2516: recurses into nested Datatype fields.
    pub(in crate::codegen_ay::chc) fn sum_datatype_field_bits(sort: &Sort) -> Option<u32> {
        Self::sum_datatype_field_bits_inner(sort, 0)
    }
    /// Recursive helper with depth guard against infinite recursion.
    pub(in crate::codegen_ay::chc) fn sum_datatype_field_bits_inner(
        sort: &Sort,
        depth: u32,
    ) -> Option<u32> {
        const MAX_DEPTH: u32 = 16;
        if depth > MAX_DEPTH {
            return None;
        }
        let dt = sort.datatype_sort()?;
        let ctor = dt.constructors.first()?;
        let mut total: u32 = 0;
        for field in &ctor.fields {
            if field.sort.is_bool() {
                // Bool fields occupy 1 byte in Rust (not 1 bit)
                total = total.checked_add(8)?;
            } else if let Some(w) = field.sort.bitvec_width() {
                total = total.checked_add(w)?;
            } else if field.sort.is_datatype() {
                // Recurse into nested struct fields (Part of #2516)
                let nested_bits = Self::sum_datatype_field_bits_inner(&field.sort, depth + 1)?;
                total = total.checked_add(nested_bits)?;
            } else {
                // Non-scalar, non-struct field (Array, Int, Real) —
                // cannot compute flat bitvec width
                return None;
            }
        }
        Some(total)
    }
    /// Recover the element type for an unsized `str`/slice tail wrapped by an ADT or tuple.
    ///
    /// CHC heap modeling reasons about slice-tail DSTs at the tail element
    /// granularity, so wrapper types like `struct Inner { inner: [u8] }` inherit
    /// the same byte-level layout as their tail.
    pub(in crate::codegen_ay::chc) fn unsized_slice_tail_elem_ty(
        &self,
        ty: rustc_public::ty::Ty,
    ) -> Option<rustc_public::ty::Ty> {
        let ty = self.resolve_body_ty(ty);
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Slice(elem_ty)) => Some(elem_ty),
            TyKind::RigidTy(RigidTy::Str) => Some(rustc_public::ty::Ty::unsigned_ty(UintTy::U8)),
            TyKind::RigidTy(RigidTy::Pat(base_ty, ..)) => self.unsized_slice_tail_elem_ty(base_ty),
            TyKind::RigidTy(RigidTy::Adt(def, args))
                if def.kind() != rustc_public::ty::AdtKind::Enum =>
            {
                let fields = def.variants().first()?.fields();
                let last_field = fields.last()?;
                self.unsized_slice_tail_elem_ty(last_field.ty_with_args(&args))
            }
            TyKind::RigidTy(RigidTy::Tuple(elems)) => {
                self.unsized_slice_tail_elem_ty(*elems.last()?)
            }
            _ => None, // external enum: TyKind
        }
    }
    /// Recover exact field offsets for unsized slice/`str`-tail wrappers via rustc's
    /// internal layout query when the stable `ty.layout()` helper declines them.
    pub(in crate::codegen_ay::chc) fn resolve_unsized_slice_tail_field_offset(
        &self,
        ty: rustc_public::ty::Ty,
        field_idx: usize,
    ) -> Option<u64> {
        self.unsized_slice_tail_elem_ty(ty)?;

        let internal_ty = rustc_internal::internal(self.tcx, ty);
        let layout = self
            .tcx
            .layout_of(TypingEnv::fully_monomorphized().as_query_input(internal_ty))
            .ok()?;
        let rustc_abi::FieldsShape::Arbitrary { offsets, .. } = &layout.fields else {
            return None;
        };
        let offset =
            offsets.get(rustc_abi::FieldIdx::from_usize(field_idx)).map(|off| off.bytes())?;
        debug!(
            ?ty,
            field_idx, offset, "resolved unsized slice-tail field offset from internal layout"
        );
        Some(offset)
    }

    /// Compute the memory-array element sort for a type. Flattens Datatype
    /// sorts (ay#1766) to bitvec and unwraps Array sorts (#4152).
    #[must_use]
    pub(in crate::codegen_ay::chc) fn elem_sort_for_memory_array(
        &self,
        ty: rustc_public::ty::Ty,
    ) -> Sort {
        let ty = self.resolve_body_ty(ty);
        // Part of #3589: `dyn Trait` maps to type_key "u8" (see type_key_for_ty),
        // but get_type_size resolves the concrete tail type, producing BV16 (or
        // whatever the concrete type's size is). This contaminates the "u8" array
        // with the wrong element sort. Short-circuit: return BV8 for Dynamic types
        // since they share the "u8" partition and must match actual u8 stores.
        if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
            return Sort::bitvec(8);
        }

        // Part of #2516 Step 1: Consult type_arrays registry before the
        // full translate_ty → get_type_size → sum_datatype_field_bits pipeline.
        // If this type was already resolved by a prior call (e.g., from
        // collect_deref_type_arrays or collect_local_type_arrays), reuse
        // the cached sort. This eliminates duplicate fallback warnings and
        // ensures consistency across multiple accesses to the same type.
        let type_key = Self::type_key_for_ty(ty);
        if let Some((_arr_name, cached_sort)) = self.heap_state.type_arrays.get(type_key.as_ref()) {
            return cached_sort.clone();
        }

        let result = match Self::translate_ty(ty) {
            Some(sort) if !sort.is_datatype() => sort,
            Some(datatype_sort) => {
                // Datatype sort — flatten to bitvec based on actual type size
                // to avoid ay#1766 while preserving sort width accuracy.
                if let Some(size_bytes) = self.get_type_size(ty) {
                    match size_bytes.checked_mul(8).and_then(|b| u32::try_from(b).ok()) {
                        Some(w) if w > 0 => Sort::bitvec(w),
                        Some(_) => bool_sort(), // ZST: use Bool
                        None => {
                            // Overflow: type too large for bitvec — use string-based fallback
                            Self::sort_from_type_key(&type_key)
                        }
                    }
                } else if let Some(total_bits) = Self::sum_datatype_field_bits(&datatype_sort) {
                    // Layout unavailable but Datatype sort has field widths —
                    // compute total bitvec width from field sorts.
                    // Part of #2323: recovers user-defined structs (Point, Watcher, etc.)
                    // that get_type_size cannot resolve in standalone driver mode.
                    if total_bits > 0 {
                        Sort::bitvec(total_bits)
                    } else {
                        bool_sort() // ZST
                    }
                } else {
                    // Both layout and field-sum failed — string-based fallback
                    Self::sort_from_type_key(&type_key)
                }
            }
            None => {
                // translate_ty failed — try get_type_size to produce a correctly-sized
                // bitvec before falling to the string-based sort_from_type_key.
                // This recovers user-defined structs where ty.layout() succeeds but
                // translate_adt_ty fails (e.g., complex generics, foreign types).
                // Part of #2323: reduces opaque Array(bv64, bv8) fallback hits.
                if let Some(size_bytes) = self.get_type_size(ty) {
                    match size_bytes.checked_mul(8).and_then(|b| u32::try_from(b).ok()) {
                        Some(w) if w > 0 => return Sort::bitvec(w),
                        Some(_) => return bool_sort(), // ZST
                        None => {} // Overflow — fall through to sort_from_type_key
                    }
                }
                Self::sort_from_type_key(&type_key)
            }
        };

        // Part of #4152: unwrap Array sorts to their element sort — regions already
        // provide Array(addr → elem) structure; nested arrays cause sort mismatches.
        if let Some(arr) = result.array_sort() { arr.element_sort.clone() } else { result }
    }

    /// Returns true if a type key with underscores is a single compound element
    /// rather than a multi-element tuple encoding.
    ///
    /// Type keys like `ptr_u8`, `ref_i32`, `arr_u64`, `slice_bool` are single
    /// compound elements that happen to contain underscores. Without this check,
    /// `tuple_ptr_u8` would be misclassified as a multi-element tuple instead
    /// of a single-element `(*mut u8,)` wrapper. (Part of #2315)
    pub(in crate::codegen_ay::chc) fn is_compound_type_key(key: &str) -> bool {
        // Known compound-key prefixes that produce underscore-containing keys
        key.starts_with("ref_")
            || key.starts_with("ptr_")
            || key.starts_with("param_")
            || key.starts_with("arr_")
            || key.starts_with("slice_")
            || key.starts_with("tuple_")
            || key.starts_with("std_")
            || key.starts_with("kani_")
            || key.starts_with("Vec_")
            || key.starts_with("Box_")
            || key.starts_with("NonNull_")
            || key.starts_with("Unique_")
            || key.starts_with("coro_")
            || key.starts_with("closure_")
    }

    /// Converts a type key string back to a AY sort.
    ///
    /// Used during type array pre-allocation to ensure element sorts match
    /// what build_memory_store expects. Part of #905.
    ///
    /// Dispatch is table-driven: exact string matches use binary search over
    /// [`EXACT_TYPE_KEY_SORTS`], then prefix/contains patterns are checked via
    /// [`PREFIX_TYPE_KEY_RULES`]. This replaces the former 47-arm match.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn sort_from_type_key(type_key: &str) -> Sort {
        if let Some(sort) = Self::try_sort_from_type_key(type_key) {
            return sort;
        }

        // Phase 3: fallback for unknown type keys — opaque byte-array payload.
        // Part of #1459 kept crash-resilience; #2315 strengthens soundness by
        // avoiding a guessed scalar width (old fallback: bv32).
        record_type_sort_fallback("sort_from_type_key unknown type key");
        warn!(
            type_key,
            "sort_from_type_key: unknown type key, using opaque byte-array fallback sort"
        );
        Self::unknown_type_key_fallback_sort()
    }

    /// Table-driven phases of [`Self::sort_from_type_key`] without the
    /// recording Phase-3 fallback: `None` means the string key alone cannot
    /// name a sort. Callers that still hold the concrete `Ty` (e.g.
    /// stub-internal type-array predeclaration) use this to resolve a
    /// layout-accurate sort via `elem_sort_for_memory_array` instead of
    /// recording a PROOF-demoting `type_sort_fallback` for a type whose
    /// layout is in fact known (e.g. libc's all-lowercase
    /// `pthread_mutex_t`, which the uppercase-ADT catch-all rule misses).
    #[must_use]
    pub(in crate::codegen_ay::chc) fn try_sort_from_type_key(type_key: &str) -> Option<Sort> {
        // Phase 1: exact-match lookup via binary search (O(log n)).
        if let Ok(idx) = EXACT_TYPE_KEY_SORTS.binary_search_by_key(&type_key, |&(k, _)| k) {
            return Some((EXACT_TYPE_KEY_SORTS[idx].1)());
        }

        // Phase 2: prefix/contains pattern rules, checked in priority order.
        for rule in PREFIX_TYPE_KEY_RULES {
            if (rule.matches)(type_key) {
                return Some((rule.sort)(type_key));
            }
        }

        None
    }

    /// Generates a type key string for type-indexed memory partitioning.
    ///
    /// Type keys group memory accesses by type signature for scalability.
    /// Returns `Cow::Borrowed` for common scalar types (no allocation) and
    /// `Cow::Owned` for compound types that require formatting.
    pub(in crate::codegen_ay::chc) fn type_key_for_ty(
        ty: rustc_public::ty::Ty,
    ) -> Cow<'static, str> {
        let ty = unwrap_heap_transparent_ty(ty);
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Bool) => Cow::Borrowed("bool"),
            TyKind::RigidTy(RigidTy::Char) => Cow::Borrowed("char"),
            TyKind::RigidTy(RigidTy::Int(int_ty)) => Cow::Borrowed(match int_ty {
                IntTy::Isize => "isize",
                IntTy::I8 => "i8",
                IntTy::I16 => "i16",
                IntTy::I32 => "i32",
                IntTy::I64 => "i64",
                IntTy::I128 => "i128",
            }),
            TyKind::RigidTy(RigidTy::Uint(uint_ty)) => Cow::Borrowed(match uint_ty {
                UintTy::Usize => "usize",
                UintTy::U8 => "u8",
                UintTy::U16 => "u16",
                UintTy::U32 => "u32",
                UintTy::U64 => "u64",
                UintTy::U128 => "u128",
            }),
            TyKind::RigidTy(RigidTy::Float(float_ty)) => Cow::Borrowed(match float_ty {
                FloatTy::F16 => "f16",
                FloatTy::F32 => "f32",
                FloatTy::F64 => "f64",
                FloatTy::F128 => "f128",
            }),
            // Part of #3608: Map `dyn Trait` to `u8` for type-indexed memory
            // partitioning. `dyn Trait` is unsized and only appears behind
            // pointers/Box; Rust represents the pointed-to memory as raw
            // bytes (u8) with vtable metadata in the fat pointer. Without
            // this, `Box<dyn Trait>` stores use a debug-format type key
            // (ty_Ty...Dynamic...) while loads use the MIR-erased `Box<u8>`
            // key — different arrays, causing unconstrained reads (CTREX).
            // The #3589 deref handler resolves `dyn Trait` to concrete types
            // BEFORE calling type_key_for_ty, so field-level loads are not
            // affected. This only fires when `dyn Trait` appears unresolved
            // as a generic arg (e.g., Box<dyn Trait> stored as a whole value).
            TyKind::RigidTy(RigidTy::Dynamic(..)) => Cow::Borrowed("u8"),
            // Part of #3596: unresolved generic params appear in non-monomorphized
            // SIMD helper bodies (`[T; N]`, `&[T; N]`). Give them a stable key that
            // `sort_from_type_key` can reconstruct instead of falling through to the
            // opaque debug-format fallback.
            TyKind::Param(param_ty) => {
                let mut key = String::with_capacity(16);
                key.push_str("param_");
                key.push_str(&param_ty.index.to_string());
                Cow::Owned(key)
            }
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => {
                Cow::Owned(prefix_type_key("ref_", Self::type_key_for_ty(inner)))
            }
            TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
                Cow::Owned(prefix_type_key("ptr_", Self::type_key_for_ty(inner)))
            }
            TyKind::RigidTy(RigidTy::Array(elem, _)) => {
                // Part of #3318: arrays share type key with slices so that
                // unsizing coercion ([T; N] → [T]) reads from the same memory.
                Cow::Owned(prefix_type_key("slice_", Self::type_key_for_ty(elem)))
            }
            TyKind::RigidTy(RigidTy::Slice(elem)) => {
                Cow::Owned(prefix_type_key("slice_", Self::type_key_for_ty(elem)))
            }
            // Part of #3655: str is layout-identical to [u8]. Map to the same
            // type key as Slice(u8) so stores via [u8] and loads via str use
            // the same memory partition. Without this, str falls through to
            // the debug-format catchall, creating a disconnected array that
            // causes Genuine CTREX on Box<str> heap operations.
            TyKind::RigidTy(RigidTy::Str) => Cow::Borrowed("slice_u8"),
            TyKind::RigidTy(RigidTy::Tuple(elems)) if elems.is_empty() => Cow::Borrowed("unit"),
            TyKind::RigidTy(RigidTy::Tuple(elems)) => {
                // Non-empty tuple: include element types (#544 audit)
                let mut key = String::from("tuple");
                for e in &elems {
                    key.push('_');
                    key.push_str(&Self::type_key_for_ty(*e));
                }
                Cow::Owned(key)
            }
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                // Use ADT name + generic args for type key (#544 audit)
                // Without args, Vec<i32> and Vec<String> alias to same array
                // Part of #2267: single-pass sanitization instead of chained .replace()
                // (was 4 intermediate String allocations, now 1).
                // Part of #3325: prepend crate name for non-std crates.
                let crate_info = def.krate();
                let name = if crate_info.is_local || is_std_crate(&crate_info.name) {
                    def.name()
                } else {
                    format!("{}_{}", crate_info.name, def.name())
                };
                let mut result = String::with_capacity(name.len() + 16);
                let mut prev_colon = false;
                for c in name.chars() {
                    match c {
                        ':' => {
                            if !prev_colon {
                                // First colon of `::` — emit `_`, wait for second.
                                result.push('_');
                                prev_colon = true;
                            } else {
                                // Second colon of `::` — skip (already emitted `_`).
                                prev_colon = false;
                            }
                        }
                        '<' | ',' => {
                            prev_colon = false;
                            result.push('_');
                        }
                        '>' => {
                            prev_colon = false;
                        }
                        _ => {
                            prev_colon = false;
                            result.push(c);
                        }
                    }
                }

                // Include type arguments if any
                for arg in &args.0 {
                    if let GenericArgKind::Type(ty) = arg {
                        result.push('_');
                        result.push_str(&Self::type_key_for_ty(*ty));
                    }
                }
                Cow::Owned(result)
            }
            // Part of #3159: Foreign types (extern type) — extract name for
            // recognizable type key. VTable and other foreign types get stable keys
            // instead of opaque debug-format fallbacks.
            TyKind::RigidTy(RigidTy::Foreign(def)) => {
                // Part of #2267: single-pass sanitization (was 3 intermediate Strings).
                // Uses prev_colon to collapse `::` into single `_` (same as ADT path).
                let name = def.name();
                let mut result = String::with_capacity(8 + name.len());
                result.push_str("foreign_");
                let mut prev_colon = false;
                for c in name.chars() {
                    match c {
                        ':' => {
                            if !prev_colon {
                                result.push('_');
                                prev_colon = true;
                            } else {
                                prev_colon = false;
                            }
                        }
                        '<' => {
                            prev_colon = false;
                            result.push('_');
                        }
                        '>' => {
                            prev_colon = false;
                        }
                        _ => {
                            prev_colon = false;
                            result.push(c);
                        }
                    }
                }
                Cow::Owned(result)
            }
            // Coroutine/closure types: stable type keys for heap store/load matching.
            TyKind::RigidTy(RigidTy::Coroutine(def, args)) => {
                Cow::Owned(def_type_key("coro_", &def.name(), &args.0))
            }
            TyKind::RigidTy(RigidTy::Closure(def, args)) => {
                Cow::Owned(def_type_key("closure_", &def.name(), &args.0))
            }
            TyKind::RigidTy(RigidTy::CoroutineClosure(def, args)) => {
                Cow::Owned(def_type_key("coro_closure_", &def.name(), &args.0))
            }
            TyKind::RigidTy(RigidTy::CoroutineWitness(def, args)) => {
                Cow::Owned(def_type_key("coro_witness_", &def.name(), &args.0))
            }
            _ => {
                // external enum: TyKind
                // Fallback: use debug format with sanitization directly into buffer.
                // Part of #2267: single-allocation via fmt::Write adapter.
                struct Sanitize<'a>(&'a mut String);
                impl std::fmt::Write for Sanitize<'_> {
                    fn write_str(&mut self, s: &str) -> std::fmt::Result {
                        self.0.extend(
                            s.chars().map(|c| if c.is_ascii_alphanumeric() { c } else { '_' }),
                        );
                        Ok(())
                    }
                }
                let mut key = String::from("ty_");
                use std::fmt::Write;
                write!(Sanitize(&mut key), "{ty:?}").ok();
                Cow::Owned(key)
            }
        }
    }

    pub(in crate::codegen_ay::chc) fn type_key_for_body_ty(
        &self,
        ty: rustc_public::ty::Ty,
    ) -> Cow<'static, str> {
        Self::type_key_for_ty(self.resolve_body_ty(ty))
    }
}

/// Part of #3325: std-library crates whose type keys must not be crate-prefixed.
fn is_std_crate(name: &str) -> bool {
    matches!(
        name,
        "std" | "core" | "alloc" | "proc_macro" | "compiler_builtins" | "kani" | "kani_core"
    )
}

/// Build a type key by prepending a prefix to a recursive type key result.
/// Avoids `format!("{prefix}{inner}")` by writing directly into a pre-sized buffer.
fn prefix_type_key(prefix: &str, inner: Cow<'_, str>) -> String {
    let mut key = String::with_capacity(prefix.len() + inner.len());
    key.push_str(prefix);
    key.push_str(&inner);
    key
}

/// Build a type key for coroutine/closure types: prefix + sanitized name + generic args.
fn def_type_key(prefix: &str, name: &str, args: &[GenericArgKind]) -> String {
    let mut key = String::with_capacity(prefix.len() + name.len() + 16);
    key.push_str(prefix);
    key.extend(name.chars().map(|c| if c.is_ascii_alphanumeric() { c } else { '_' }));
    for arg in args {
        if let GenericArgKind::Type(ty) = arg {
            key.push('_');
            key.push_str(&ChcCtx::type_key_for_ty(*ty));
        }
    }
    key
}

// Table-driven dispatch tables extracted to separate module for 500 LOC limit.
use super::memory_type_key_tables::{EXACT_TYPE_KEY_SORTS, PREFIX_TYPE_KEY_RULES};
