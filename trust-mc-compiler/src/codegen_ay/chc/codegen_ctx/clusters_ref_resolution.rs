// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// RefResolution cluster for ChcCtx reference/pointer resolution state.
// Extracted from `clusters.rs` — Part of #4206.

use ay_bindings::{Expr, Sort};
use rustc_public::mir::alloc::AllocId;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use super::types::RefTarget;
use crate::codegen_ay::provenance::Loc;

/// Reference resolution state for deref chain, BigInt/BigRational, static,
/// and const-ref lookups.
///
/// Encapsulates how MIR reference locals map to their underlying values
/// (BigInt locals, deref chain targets, arg-backed pointees, static state
/// vars, const scalar values, const discriminants).
///
/// Part of #2880 P3: RefResolution extraction (8 fields -> 1 cluster field).
pub(in crate::codegen_ay::chc) struct RefResolution {
    /// Maps reference locals to the BigInt local they point to (Part of #734).
    pub(in crate::codegen_ay::chc) bigint_ref_targets: HashMap<usize, usize>,

    /// Maps reference locals to the BigRational local they point to (Part of #911).
    pub(in crate::codegen_ay::chc) bigrational_ref_targets: HashMap<usize, usize>,

    /// Maps reference locals to their resolved targets for deref chain resolution.
    /// Part of #1712: Extended to handle `_ref = &((*other_ref).field)` patterns.
    pub(in crate::codegen_ay::chc) ref_targets: HashMap<usize, RefTarget>,

    /// Maps argument reference locals to their pointee state_vars vector index.
    /// Part of #2496: implicit `&T`/`&mut T` argument references.
    pub(in crate::codegen_ay::chc) ref_arg_pointee_idx: HashMap<usize, usize>,

    /// Maps wrapper-typed argument locals and their ref-bearing field index to
    /// the auxiliary pointee state-var index.
    ///
    /// Covers shapes like `Pin<&mut T>` where the function argument itself is
    /// not a reference local, but copying field `0` yields one.
    pub(in crate::codegen_ay::chc) arg_wrapper_field_pointee_idx: HashMap<(usize, usize), usize>,

    /// Maps Pin/ref locals in coroutine resume chains to the auxiliary
    /// state-var index that stores the concrete coroutine root expression.
    ///
    /// Part of #3807: pre-register coroutine roots for `Pin<&mut Coroutine>`
    /// arguments and propagate that root through copy/reborrow chains.
    pub(in crate::codegen_ay::chc) coroutine_root_map: HashMap<usize, usize>,

    /// Maps locals holding a pointer to a static item to the state variable
    /// vec index for that static's value (Part of #428).
    pub(in crate::codegen_ay::chc) static_ref_to_state_idx: HashMap<usize, usize>,

    /// Maps static state variable vec_idx to its initial value expression (Part of #428).
    pub(in crate::codegen_ay::chc) static_initial_values: HashMap<usize, Expr>,

    /// P2-S1: partial entry-rule pin constraints for interior-mutable
    /// immutable statics under a contract CHECK harness. Each Expr pins ONLY
    /// the non-UnsafeCell (Freeze) fields of the static's state variable to
    /// the initializer; UnsafeCell-covered parts stay unconstrained (havoc).
    /// Field-precise (Kani over-approximates by havocking the whole static —
    /// see kani tests/kani/FunctionContracts/fixme_static_interior_mut.rs).
    pub(in crate::codegen_ay::chc) contract_static_partial_pins: Vec<Expr>,

    /// Immutable static-backed referent values keyed by the static state-var index.
    ///
    /// Reuses the same Array/Datatype expressions later copied into
    /// `const_ref_values`, but keeps one canonical seed per static so alias locals
    /// propagated via `static_ref_to_state_idx` can recover the referent even when
    /// they did not directly originate from the constant assignment statement.
    pub(in crate::codegen_ay::chc) static_ref_value_seeds: HashMap<usize, Expr>,

    /// Pointer-width length metadata paired with `static_ref_value_seeds`.
    ///
    /// Used for immutable slice/str-backed statics whose referent value is seeded
    /// into `const_ref_values` but still needs concrete `PtrMetadata`/slice length.
    pub(in crate::codegen_ay::chc) static_ref_len_seeds: HashMap<usize, Expr>,

    /// Tracks which static state vars correspond to `static mut`.
    ///
    /// Some call handlers can soundly fold immutable statics to their cached
    /// initializer literals, but mutable statics must keep state-variable
    /// semantics so prior stores remain visible.
    pub(in crate::codegen_ay::chc) mutable_static_state_idxs: HashSet<usize>,

    /// Concrete address expressions for each unique static, keyed by AllocId.
    /// Each static gets a distinct obj_id in the split-pointer scheme (BV32++BV32),
    /// making `&A as *const _ != &B as *const _` decidable.
    /// Part of #3496 Bug B: static address distinctness.
    pub(in crate::codegen_ay::chc) static_address_exprs: HashMap<AllocId, Expr>,

    /// Maps reference locals assigned from constant references to unit enums (Part of #1905).
    pub(in crate::codegen_ay::chc) const_ref_discriminants: HashMap<usize, u64>,

    /// Maps reference locals assigned from constant references to scalar values (Part of #1919).
    pub(in crate::codegen_ay::chc) const_ref_values: HashMap<usize, Expr>,

    /// Maps reference locals to full Slice datatype expressions (Part of #3012).
    /// When VecAsSlice returns a bv64 pointer (because translate_ty maps &[T] to bv64),
    /// the Slice(fld_ptr, fld_len, fld_data) is stored here so that downstream
    /// VecIter/VecIterMut handlers can reconstruct the Slice for make_vec_into_iter_chc.
    pub(in crate::codegen_ay::chc) const_ref_slice_views: HashMap<usize, Expr>,

    /// Memory array initializations needed for promoted constant references.
    /// Each entry: (type_key, elem_sort, value_expr, promoted_obj_id, byte_offset).
    /// Different promoted constants must use distinct object IDs so their typed
    /// memory seeds do not collide in the entry rule.
    /// Part of #2958: byte-level memory model initialization.
    /// Part of #2986: byte_offset enables per-element array constant initialization.
    pub(in crate::codegen_ay::chc) const_ref_memory_inits: Vec<(Arc<str>, Sort, Expr, u32, u64)>,

    /// Promoted constant object IDs keyed by local.
    ///
    /// Array-backed promoted refs sometimes lower to pointer-typed locals. When
    /// statement lowering needs the concrete promoted address for such a local,
    /// this map provides the exact object ID assigned during const-ref discovery.
    pub(in crate::codegen_ay::chc) const_ref_promoted_obj_ids: HashMap<usize, u32>,

    /// Maps promoted constant allocation IDs to their per-constant addresses.
    /// When `pointer_scalar_expr` translates a promoted `const &T` reference,
    /// it needs the per-constant address (not the shared obj_id=1 fallback).
    /// Part of #3860: address mismatch between translate_constant and entry rule.
    pub(in crate::codegen_ay::chc) promoted_const_alloc_addresses:
        HashMap<rustc_public::mir::alloc::AllocId, Expr>,

    /// Locals that received heap allocation results (Part of #3012).
    /// These locals hold pointers from exchange_malloc/RustAlloc stubs, which are
    /// always non-NULL by construction (obj_id >= 2, pointer = concat(obj_id, 0)).
    /// Used to skip false-positive NullPointerDereference MIR asserts.
    pub(in crate::codegen_ay::chc) alloc_result_locals: HashSet<usize>,

    /// Maps IndexMut destination locals to their collection + index context.
    /// When `*dest = val` is encountered, the store propagates to the Vec's
    /// `fld_data` array as `data' = store(data, idx, val)`.
    /// Part of #3348: Vec IndexMut CHC stub.
    pub(in crate::codegen_ay::chc) collection_mut_refs:
        HashMap<usize, super::types::CollectionMutRef>,

    /// Maps immutable `Index::index` destination locals to their collection +
    /// index context — the READ-side analog of `collection_mut_refs`.
    ///
    /// Contract modifies clauses name element targets with immutable borrows
    /// (`#[kani::modifies(&v[0])]`), which lower to `Index::index` before the
    /// replace shim casts the reference to `*mut T` via
    /// `kani::internal::Pointer::assignable`. Consumed ONLY by the
    /// `write_any_slim` collection-havoc lane (never by ordinary deref-store
    /// handlers, which must not see read-only index results).
    pub(in crate::codegen_ay::chc) collection_index_refs:
        HashMap<usize, super::types::CollectionMutRef>,

    /// Maps VecAsSlice/deref_mut destination locals to the source Vec local.
    /// Set during VecAsSlice call handling; consumed by IndexMut to find the
    /// Vec whose `fld_data` array must be updated on deref store.
    /// Part of #3348: Vec IndexMut CHC stub.
    pub(in crate::codegen_ay::chc) slice_to_vec_local: HashMap<usize, usize>,

    /// Field projections from the `slice_to_vec_local` target to the actual Vec.
    ///
    /// When `deref_mut` is called on a Vec accessed through a struct field
    /// (e.g., `_ref = &mut (*_self).marks`), `slice_to_vec_local` maps to the
    /// struct local (`_self`), but the Vec is at `_self.marks`. This map carries
    /// the field projections so that `register_index_mut_tracking` can reconstruct
    /// the full path from struct to Vec for `handle_struct_embedded_vec_store`.
    /// Part of #3439: struct-projected collection IndexMut.
    pub(in crate::codegen_ay::chc) slice_to_vec_field_projections:
        HashMap<usize, Vec<rustc_public::mir::ProjectionElem>>,

    /// Maps VecIter/VecIntoIter/VecIterMut destination locals to the source
    /// collection local. Set during VecIter call handling; consumed by
    /// VecExtendFromSlice to resolve source length from iterator arguments.
    /// Part of #3348: VecExtendFromSlice source length resolution.
    pub(in crate::codegen_ay::chc) iter_to_collection_local: HashMap<usize, usize>,

    /// Locals holding raw pointers forwarded through call dispatch (e.g.,
    /// `UnsafeCell::get`). These locals have `ref_targets` entries set by
    /// call handlers and should bypass the Mem-level raw-pointer deref guard.
    /// Propagated through Copy/Move/Cast of raw pointer locals.
    /// Part of #3452: stable atomic abstraction boundary.
    pub(in crate::codegen_ay::chc) call_forwarded_raw_ptrs: HashSet<usize>,

    /// Maps collection get() destination locals to their raw pre-promotion
    /// values. When `promote_value_to_ref` wraps a scalar V in a virtual
    /// pointer for Option<&V>, the original V is stored here so that
    /// `Option::copied()` can skip the memory deref and use the value directly.
    /// Part of #3348: BTreeMap get→copied→unwrap_or chain fix.
    pub(in crate::codegen_ay::chc) promoted_raw_values: HashMap<usize, Expr>,

    /// Maps subslice destination locals to the start offset expression.
    /// When `&source[start..end]` produces a subslice, the source backing array
    /// is stored in `const_ref_values[dest]` and the start offset is stored here.
    /// Downstream `SliceIndex` applies the offset: `source.select(idx + offset)`.
    /// Part of #3495: range subslice fat pointer constraint fix.
    pub(in crate::codegen_ay::chc) subslice_offset: HashMap<usize, Expr>,

    /// Maps subslice destination locals to the length expression (`end - start`).
    /// Consumed by `translate_ptr_metadata` to resolve `PtrMetadata` on subslice
    /// results without requiring compile-time-constant Range bounds.
    /// Part of #3495: range subslice fat pointer constraint fix.
    pub(in crate::codegen_ay::chc) subslice_len: HashMap<usize, Expr>,

    /// Caches subslice materialization addresses by (provenance_local, start_const).
    /// When two subslice operations share the same provenance and start offset,
    /// they reuse the same data address, preserving fat pointer identity.
    /// Part of #4030: source-derived addresses for pointer comparison.
    ///
    /// The value is a [`Loc`]: every entry is written from a
    /// `SubsliceMaterialization::fresh_addr`, which is an address by
    /// construction, and every read feeds one straight back in as the next
    /// materialization's `addr_override`.
    pub(in crate::codegen_ay::chc) subslice_addr_cache: HashMap<(usize, u64), Loc>,

    /// Memory array initializations for static variables.
    /// Each entry: (type_key, elem_sort, init_value, addr_expr) for mirroring
    /// static initial values into typed memory arrays in the entry rule.
    /// Part of #3496 Phase 5: static memory mirroring.
    pub(in crate::codegen_ay::chc) static_memory_inits: Vec<(Arc<str>, Sort, Expr, Expr)>,

    /// Heap allocation layout metadata for static variables:
    /// `(obj_id, size_bytes, align_bytes)`.
    ///
    /// Static allocations get obj_ids from `next_alloc_id()` for address
    /// distinctness but were missing `obj_size[obj_id]` entry constraints,
    /// causing spurious CTREX on inline drop body dealloc safety checks.
    /// Family 3 extends this metadata with the requested base alignment so the
    /// entry rule can make the static address alignment explicit.
    /// Part of #3793: static allocation obj_size constraints.
    pub(in crate::codegen_ay::chc) static_alloc_sizes: Vec<(u32, u32, u64)>,

    /// Maps pointer locals derived from argument reference deref chains to
    /// the argument's pointee state variable index.
    ///
    /// Handles patterns like `as_array(&self) -> &[T; N]` where a raw pointer
    /// is created from `&raw const (*self)`, then cast to a different pointer
    /// type, then dereferenced. Since argument references (`&self`) are not
    /// seeded in `ref_targets` (Part of #2496), the normal ref propagation
    /// can't follow these chains. This map bridges the gap by tracking which
    /// pointer locals are derived from argument reference pointees.
    ///
    /// Part of #3596: SIMD pointer cast chain resolution.
    pub(in crate::codegen_ay::chc) ptr_deref_to_arg_pointee: HashMap<usize, usize>,
}

impl RefResolution {
    pub(in crate::codegen_ay::chc) fn new() -> Self {
        Self {
            bigint_ref_targets: HashMap::new(),
            bigrational_ref_targets: HashMap::new(),
            ref_targets: HashMap::new(),
            ref_arg_pointee_idx: HashMap::new(),
            arg_wrapper_field_pointee_idx: HashMap::new(),
            coroutine_root_map: HashMap::new(),
            static_ref_to_state_idx: HashMap::new(),
            static_initial_values: HashMap::new(),
            contract_static_partial_pins: Vec::new(),
            static_ref_value_seeds: HashMap::new(),
            static_ref_len_seeds: HashMap::new(),
            mutable_static_state_idxs: HashSet::new(),
            static_address_exprs: HashMap::new(),
            const_ref_discriminants: HashMap::new(),
            const_ref_values: HashMap::new(),
            const_ref_slice_views: HashMap::new(),
            const_ref_memory_inits: Vec::new(),
            const_ref_promoted_obj_ids: HashMap::new(),
            promoted_const_alloc_addresses: HashMap::new(),
            alloc_result_locals: HashSet::new(),
            collection_mut_refs: HashMap::new(),
            collection_index_refs: HashMap::new(),
            slice_to_vec_local: HashMap::new(),
            slice_to_vec_field_projections: HashMap::new(),
            iter_to_collection_local: HashMap::new(),
            call_forwarded_raw_ptrs: HashSet::new(),
            promoted_raw_values: HashMap::new(),
            subslice_offset: HashMap::new(),
            subslice_len: HashMap::new(),
            subslice_addr_cache: HashMap::new(),
            static_memory_inits: Vec::new(),
            static_alloc_sizes: Vec::new(),
            ptr_deref_to_arg_pointee: HashMap::new(),
        }
    }
}
