// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// RefResolution cluster for ChcCtx reference/pointer resolution state.
// Extracted from `clusters.rs` — Part of #4206.

use ay_bindings::{Expr, Sort};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use super::types::RefTarget;
use crate::codegen_ay::provenance::Loc;

/// The object a constant-pointer local points into (D4).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) struct ConstRefObject {
    /// The target's object id (`global_objects`).
    pub(in crate::codegen_ay::chc) obj_id: u32,
    /// The byte offset the pointer carries into its target.
    pub(in crate::codegen_ay::chc) offset: u64,
    /// The pointer itself (target + this offset), when known exactly: lets a
    /// known delta RE-DECODE the window there (D10,
    /// `const_pointer::fixed_pointee_at`) instead of copying a fact about
    /// another window.
    pub(in crate::codegen_ay::chc) ptr: Option<crate::codegen_ay::shared::const_pointer::ConstPtr>,
    /// For a `&&str` constant: the inner `&str`'s data pointer (its string's
    /// object and offset), which a deref of the outer pointer reads.
    pub(in crate::codegen_ay::chc) nested: Option<(u32, u64)>,
}

impl ConstRefObject {
    /// This pointer moved by `delta` bytes (the same object).
    pub(in crate::codegen_ay::chc) fn moved(&self, delta: i128) -> Option<ConstRefObject> {
        let offset = u64::try_from(i128::from(self.offset).checked_add(delta)?).ok()?;
        Some(ConstRefObject {
            obj_id: self.obj_id,
            offset,
            ptr: self.ptr.and_then(|p| p.moved(delta)),
            nested: None,
        })
    }

    /// The address `concat(obj_id, 0) + offset`.
    pub(in crate::codegen_ay::chc) fn address(&self) -> Expr {
        let base = crate::codegen_ay::chc::decl::global_objects::object_base_for(self.obj_id);
        if self.offset == 0 {
            base
        } else {
            base.bvadd(Expr::bitvec_const(
                u128::from(self.offset),
                crate::codegen_ay::types::POINTER_WIDTH,
            ))
        }
    }
}

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

    /// The static state vars whose value can CHANGE during the run: every
    /// `static mut`, and every static of a non-`Freeze` type (an atomic, a
    /// `Cell`, an `UnsafeCell`), which an `&` can still write
    /// (`shared::const_pointer::Fixedness::Live`).
    ///
    /// Some call handlers can soundly fold a FIXED static to its cached
    /// initializer literal, but a live one must keep state-variable semantics
    /// so prior stores remain visible. This held only `static mut`, so an
    /// atomic static read back its initializer after a store:
    /// `RA.store(5); ATOMS[1].load() == 2` PROVED.
    pub(in crate::codegen_ay::chc) mutable_static_state_idxs: HashSet<usize>,

    /// Each static state variable's Rust type (the static's type), for the
    /// static place path (`decl::static_path`).
    pub(in crate::codegen_ay::chc) static_state_ty: HashMap<usize, rustc_public::ty::Ty>,

    /// For a local mapped to a LIVE static's state variable through a
    /// constant pointer at an offset (D6): the path from the static's value to
    /// the part the pointer names. Absent: the whole static.
    pub(in crate::codegen_ay::chc) static_ref_paths:
        HashMap<usize, Vec<crate::codegen_ay::chc::decl::static_path::StaticPathElem>>,

    /// Static state vars a FOREIGN callee could legally write: every `static
    /// mut` plus every immutable static whose type is non-`Freeze` (interior
    /// mutability). Linked C code can reach an exported symbol without Rust
    /// ever handing it a pointer, so a call to an opaque C function must havoc
    /// these. Populated alongside `mutable_static_state_idxs`; a superset of it.
    pub(in crate::codegen_ay::chc) c_writable_static_state_idxs: HashSet<usize>,

    /// Linker SYMBOL of every foreign (`extern "C"`) static, mapped to its
    /// state slot.
    ///
    /// A `--c-lib` translation unit names an exported object by symbol; the
    /// Rust path and `#[link_name]` may disagree, so the C front-end resolves
    /// `S` through this table rather than by name matching.
    pub(in crate::codegen_ay::chc) c_symbol_static_state_idx: HashMap<String, usize>,

    /// THE object table (D1, `decl::global_objects`): one object per global
    /// allocation (constant memory or static), keyed by its identity
    /// (`shared::const_pointer::TargetKey`), minted once by `mint_object`
    /// before translation. Replaces the AllocId-keyed `static_address_exprs`
    /// and `promoted_const_alloc_addresses` and the shared object-1 fallback.
    pub(in crate::codegen_ay::chc) global_objects: HashMap<
        crate::codegen_ay::shared::const_pointer::TargetKey,
        crate::codegen_ay::chc::decl::global_objects::GlobalObject,
    >,

    /// The types the harness reads each global object at (D2), in first-noted
    /// order: the pointee types of constant pointers into it and of pointers
    /// derived from them. `seed_global_objects` seeds the fixed ones whole.
    pub(in crate::codegen_ay::chc) object_read_types:
        Vec<(crate::codegen_ay::shared::const_pointer::TargetKey, Vec<rustc_public::ty::Ty>)>,
    /// Reads noted by `&self` decoders (`note_object_read_deferred`), drained
    /// into `object_read_types`.
    pub(in crate::codegen_ay::chc) pending_object_reads: std::cell::RefCell<
        Vec<(crate::codegen_ay::shared::const_pointer::TargetKey, rustc_public::ty::Ty)>,
    >,
    /// The types the harness dereferences at (its body and pre-scanned
    /// callees, panic-only blocks excluded): every FIXED object in the read set
    /// is seeded at each of them too (D2), because a cast or byte offset reads
    /// an object at a type no constant names.
    pub(in crate::codegen_ay::chc) extra_read_types: Vec<rustc_public::ty::Ty>,
    /// Set once the entry rule's seeds are final (end of the declaration
    /// passes): a read noted later fails closed (`const_object_unseeded`).
    pub(in crate::codegen_ay::chc) object_seeding_closed: bool,
    /// Actual u8/BV8 entry cells, frozen before emission and retained after
    /// bb0 consumes the working seed vector. None marks conflicting or
    /// mismatched declarations. Later seeds/arrays cannot add authority.
    pub(in crate::codegen_ay::chc) const_ref_entry_byte_seeds: HashMap<(u32, u64), Option<Expr>>,
    /// (obj_id, type) pairs `seed_global_objects` already seeded.
    pub(in crate::codegen_ay::chc) seeded_object_types: HashSet<(u32, rustc_public::ty::Ty)>,
    /// (type_key, cell sort, obj_id, offset) cells already in
    /// `const_ref_memory_inits`. The sort is part of the cell: an array's key
    /// carries both its per-element cells and its whole-value cell at offset
    /// 0, and the entry rule seeds the one whose sort the key registered.
    pub(in crate::codegen_ay::chc) seeded_cells: HashSet<(Arc<str>, ay_bindings::Sort, u32, u64)>,

    /// Statics whose layout size and typed-memory mirror are registered (by
    /// the static collector or a callee pre-scan), so a later body does not
    /// register them twice.
    pub(in crate::codegen_ay::chc) registered_static_memory:
        HashSet<rustc_public::mir::mono::StaticDef>,

    /// The state-variable index of each static the harness keeps a state
    /// variable for, keyed by the obj_id of its object in `global_objects`. The walker's static mirror
    /// (`mirror_static_state_var_update`) writes exactly the state variable
    /// of the static a store reached; a static discovered only in a callee
    /// has an address but no state variable, and is absent.
    pub(in crate::codegen_ay::chc) static_state_idx_by_obj: HashMap<u32, usize>,

    /// For a POINTER-typed static, the address of the allocation its
    /// initializer points at, keyed by the static's state-var index.
    ///
    /// `static Z: &i32 = &14` has TWO allocations: `Z`'s own slot, which holds
    /// a pointer, and the anonymous nested allocation holding `14`. Loading
    /// `*Z_slot` yields the POINTER, so the loaded value addresses the nested
    /// allocation — not `Z`'s slot. Without this map the load inherits the
    /// slot's own object and `**Z` reads `Z`'s pointer bits as an `i32`.
    pub(in crate::codegen_ay::chc) static_pointee_addrs: HashMap<usize, Expr>,

    /// Initial value of the window a FIXED pointer-typed static points at,
    /// keyed by the STATIC's state-var index.
    pub(in crate::codegen_ay::chc) static_pointee_init_values: HashMap<usize, Expr>,

    /// THE decoded value of each fixed pointee window a pointer-typed static
    /// or promoted shared array names, keyed by (target, offset,
    /// length word, pointee type): two statics naming one window — kani's
    /// `static FOO: &[i32] = &[42]; static BAR: &[i32] = &*FOO` — denote ONE
    /// value, not two decodes with two fresh array bases whose free tails
    /// could disagree.
    pub(in crate::codegen_ay::chc) window_values: HashMap<
        (
            crate::codegen_ay::shared::const_pointer::TargetKey,
            u64,
            Option<u64>,
            rustc_public::ty::Ty,
        ),
        Expr,
    >,

    /// Maps reference locals assigned from constant references to unit enums (Part of #1905).
    pub(in crate::codegen_ay::chc) const_ref_discriminants: HashMap<usize, u64>,

    /// Maps reference locals assigned from constant references to scalar values (Part of #1919).
    pub(in crate::codegen_ay::chc) const_ref_values: HashMap<usize, Expr>,

    /// Maps reference locals to full Slice datatype expressions (Part of #3012).
    /// When VecAsSlice returns a bv64 pointer (because translate_ty maps &[T] to bv64),
    /// the Slice(fld_ptr, fld_len, fld_data) is stored here so that downstream
    /// VecIter/VecIterMut handlers can reconstruct the Slice for make_vec_into_iter_chc.
    pub(in crate::codegen_ay::chc) const_ref_slice_views: HashMap<usize, Expr>,
    /// References whose `const_ref_values` / `const_ref_slice_views` fact was
    /// dropped because the copy that carried it was not the unique producer.
    /// Deliberately NOT cleared by `clear_path_insensitive_ref_metadata`: a deref
    /// through such a local fails closed rather than loading memory at a value.
    pub(in crate::codegen_ay::chc) deref_value_fact_dropped: HashSet<usize>,
    /// Blocks where the slice `Iterator::next` stub recorded the payload-slot
    /// value fact for a local (`stmt::codegen_stmt_payload_value_fact`).
    pub(in crate::codegen_ay::chc) payload_slot_fact_sites: HashMap<usize, HashSet<usize>>,
    /// Payload value facts kept across agreeing duplicated producers, keyed by
    /// `(source, destination)`, with the source's producer blocks that must all
    /// appear in `payload_slot_fact_sites` once translation is done.
    pub(in crate::codegen_ay::chc) kept_payload_value_facts: HashMap<(usize, usize), Vec<usize>>,
    /// Reference destinations of the slice index stubs (`Index::index`,
    /// `IndexMut::index_mut`, `get_unchecked`) whose register holds the ELEMENT,
    /// not its address (`call::codegen_call_slice_index`), checked once every
    /// block is translated ([`ChcCtx::book_escaping_index_value_refs`]).
    pub(in crate::codegen_ay::chc) index_value_ref_dests: HashSet<usize>,
    /// Blocks the Small-mode transition loop skipped (no block relation, or not
    /// reachable from `bb0`): no rule leaves them, so a write there reaches no
    /// derivation.
    pub(in crate::codegen_ay::chc) untranslated_transition_blocks: HashSet<usize>,

    /// Host call blocks whose emitted result has a uniquely held, typed stack
    /// field address. The Vec buffer prescan can exclude these exact producers.
    pub(in crate::codegen_ay::chc) inline_stack_address_calls: HashSet<usize>,

    /// Memory array initializations needed for promoted constant references.
    /// Each entry: (type_key, elem_sort, value_expr, promoted_obj_id, byte_offset).
    /// Different promoted constants must use distinct object IDs so their typed
    /// memory seeds do not collide in the entry rule.
    /// Part of #2958: byte-level memory model initialization.
    /// Part of #2986: byte_offset enables per-element array constant initialization.
    pub(in crate::codegen_ay::chc) const_ref_memory_inits: Vec<(Arc<str>, Sort, Expr, u32, u64)>,

    /// The object a constant-pointer local points into and the byte OFFSET it
    /// points at (D4), keyed by local. Readers copy the whole record, never
    /// the object id alone: `concat(obj, 0)` for a pointer into the middle of
    /// an allocation is a different address.
    pub(in crate::codegen_ay::chc) const_ref_objects: HashMap<usize, ConstRefObject>,

    /// The constant-memory object a pointer local points into at an UNKNOWN
    /// or nonzero offset: PROVENANCE ONLY, for the offset alloc-bound checks
    /// (`known_obj_id_for_operand`). Never an address. A `known_alloc_ids`
    /// entry carries an implicit offset of ZERO (`codegen_stmt_fallback.rs`
    /// `try_extract_data_obj_id`), and carrying one through `ptr.add(1)` made
    /// the deref base `concat(obj, 0)`: `*ONE.add(1) == 1` PROVED.
    pub(in crate::codegen_ay::chc) const_memory_provenance: HashMap<usize, u32>,

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

    /// Maps a local holding `&((*_e).f1.f2…)` — a reference INTO a collection
    /// element — to the element location it denotes. See
    /// [`super::types::CollectionElemFieldRef`]: without it these locals fall
    /// through to the Mem-level symbolic-address mint and read a memory array
    /// the collection was never stored into.
    pub(in crate::codegen_ay::chc) collection_elem_field_refs:
        HashMap<usize, super::types::CollectionElemFieldRef>,

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

    /// The `subslice_len` / `subslice_offset` entries a walk front door hands
    /// the next walked body for its ARGUMENT locals (keyed by the callee's
    /// local index, `1 + argument position`), taken at the walk's entry.
    ///
    /// The side tables are keyed by local index, and every walked body has
    /// its own index space: a walk clears every entry of its body's locals on
    /// entry and applies only these, so an argument local the walk never
    /// writes cannot read the entry a caller walk or the host left at the
    /// same index (walker fail-closed review 6 round 2, finding 3).
    pub(in crate::codegen_ay::chc) inline_arg_subslice_seeds:
        Option<(HashMap<usize, Expr>, HashMap<usize, Expr>)>,

    /// The walked body's return-local (`_0`) `subslice_len` /
    /// `subslice_offset` entries as the last walk to end left them, captured
    /// before that walk restores the caller's entries (the fn-inline front
    /// door propagates them to its destination).
    pub(in crate::codegen_ay::chc) inline_return_subslice: (Option<Expr>, Option<Expr>),

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
    pub(in crate::codegen_ay::chc) fn clear_path_insensitive_ref_metadata(&mut self, local: usize) {
        self.bigint_ref_targets.remove(&local);
        self.bigrational_ref_targets.remove(&local);
        self.ref_targets.remove(&local);
        self.ref_arg_pointee_idx.remove(&local);
        self.coroutine_root_map.remove(&local);
        self.static_ref_to_state_idx.remove(&local);
        self.static_ref_paths.remove(&local);
        self.call_forwarded_raw_ptrs.remove(&local);
        self.const_ref_discriminants.remove(&local);
        self.const_ref_values.remove(&local);
        self.const_ref_slice_views.remove(&local);
        self.const_ref_objects.remove(&local);
        self.const_memory_provenance.remove(&local);
        self.alloc_result_locals.remove(&local);
        self.collection_mut_refs.remove(&local);
        self.collection_index_refs.remove(&local);
        self.collection_elem_field_refs.remove(&local);
        self.slice_to_vec_local.remove(&local);
        self.slice_to_vec_field_projections.remove(&local);
        self.iter_to_collection_local.remove(&local);
        self.promoted_raw_values.remove(&local);
        self.subslice_len.remove(&local);
        self.subslice_offset.remove(&local);
        self.ptr_deref_to_arg_pointee.remove(&local);
        self.arg_wrapper_field_pointee_idx.retain(|(root, _), _| *root != local);
        self.subslice_addr_cache.retain(|(provenance, _), _| *provenance != local);
    }

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
            static_state_ty: HashMap::new(),
            static_ref_paths: HashMap::new(),
            c_writable_static_state_idxs: HashSet::new(),
            c_symbol_static_state_idx: HashMap::new(),
            global_objects: HashMap::new(),
            object_read_types: Vec::new(),
            registered_static_memory: HashSet::new(),
            pending_object_reads: std::cell::RefCell::new(Vec::new()),
            extra_read_types: Vec::new(),
            object_seeding_closed: false,
            const_ref_entry_byte_seeds: HashMap::new(),
            seeded_object_types: HashSet::new(),
            seeded_cells: HashSet::new(),
            static_state_idx_by_obj: HashMap::new(),
            static_pointee_addrs: HashMap::new(),
            static_pointee_init_values: HashMap::new(),
            window_values: HashMap::new(),
            const_ref_discriminants: HashMap::new(),
            const_ref_values: HashMap::new(),
            const_ref_slice_views: HashMap::new(),
            deref_value_fact_dropped: HashSet::new(),
            payload_slot_fact_sites: HashMap::new(),
            kept_payload_value_facts: HashMap::new(),
            index_value_ref_dests: HashSet::new(),
            untranslated_transition_blocks: HashSet::new(),
            inline_stack_address_calls: HashSet::new(),
            const_ref_memory_inits: Vec::new(),
            const_ref_objects: HashMap::new(),
            const_memory_provenance: HashMap::new(),
            alloc_result_locals: HashSet::new(),
            collection_mut_refs: HashMap::new(),
            collection_index_refs: HashMap::new(),
            collection_elem_field_refs: HashMap::new(),
            slice_to_vec_local: HashMap::new(),
            slice_to_vec_field_projections: HashMap::new(),
            iter_to_collection_local: HashMap::new(),
            call_forwarded_raw_ptrs: HashSet::new(),
            promoted_raw_values: HashMap::new(),
            subslice_offset: HashMap::new(),
            subslice_len: HashMap::new(),
            inline_arg_subslice_seeds: None,
            inline_return_subslice: (None, None),
            subslice_addr_cache: HashMap::new(),
            static_memory_inits: Vec::new(),
            static_alloc_sizes: Vec::new(),
            ptr_deref_to_arg_pointee: HashMap::new(),
        }
    }
}
