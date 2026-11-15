// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Where a constant pointer points: the ONE statement of the rule, and the
//! only code in `codegen_ay` that reads a constant's relocation table.
//!
//! # The rule
//!
//! A constant pointer is what const-eval recorded. The relocation entry AT the
//! byte position of the pointer names a target allocation T, and the
//! pointer's own little-endian bytes carry an offset k. The pointer denotes
//! the address `base(T) + k`, where `base(T)` is the ONE address the lane
//! gives T for the whole harness. That address is keyed by [`TargetKey`]: a
//! static by its definition, constant memory by its allocation id, and a
//! function by its identity, only with k = 0.
//!
//! **Bytes covered by a relocation are never data.** A pointer-typed slot is
//! read only whole, at its first byte, as the pointer above. That holds
//! whether the slot is a constant's own value, an element or field of a
//! constant VALUE, or a slot inside a target's bytes. Any other read of those
//! bytes declines ([`Slot::PartialPointer`]).
//!
//! The pointee of type P occupies `T.bytes[k .. k + extent(P)]`. The extent
//! is `size_of(P)` for a sized P, and `len × size_of(elem)` from the
//! pointer's metadata word for `[elem]`/`str` ([`pointee_extent`]).
//! Relocations inside that window are rebased by −k ([`ConstRead::sub_window`]).
//! **A pointer derived from it by a known delta d addresses
//! `base(T) + k + d`, and its pointee is the window there
//! ([`fixed_pointee_at`]). A fact about one window never answers a read of
//! another.**
//!
//! The window may be DECODED into a value only when T's bytes are fixed for
//! the run ([`Fixedness::Fixed`]): constant memory, or a static that is not
//! `mut`, not foreign, `Freeze`, and evaluable. **Then the whole of T is
//! known: a lane that represents T's memory represents all of it, at every
//! offset and every type the harness reads through a pointer into T, not only
//! the window a constant named.**
//!
//! Otherwise ([`Fixedness::Live`]) the pointee is the lane's LIVE state at
//! `base(T) + k`. A lane that cannot name that state fails closed: the value
//! is unconstrained and the reason is recorded, so no counterexample through
//! it is certified. It never reads the initializer and never reads byte 0.
//!
//! **The targets a harness can reach are the transitive closure of
//! relocations from its bodies' constants through every reached target's
//! bytes ([`reachable_targets`]). Each gets its one address before
//! translation.**
//!
//! Only a pointer-TYPED constant (`&T`, `*const T`, `*mut T`, thin or fat) is
//! a constant pointer. A constant VALUE that contains pointers is a value
//! whose slots follow the slot clause.
//!
//! # Enforcement (evidence rungs)
//!
//! - Type-level, within its scope: [`ConstPtr`]'s fields are private and
//!   [`ConstPtr::address`] is the only way from it to an address; composite
//!   readers hold a [`ConstRead`], whose only byte accessors apply the slot
//!   clause, so a reader holding one cannot read relocated bytes as data and
//!   cannot drop relocations when it slices.
//! - Source lint (a TEST, `codegen_ay/test_const_pointer_single_rule.rs`): no
//!   file under `codegen_ay/` other than this one spells the relocation table,
//!   `GlobalAlloc`, `eval_initializer`, or the `ConstantKind::Allocated` /
//!   `TyConstKind::Value` entry points. It guards spellings, not semantics.
//! - Duals (TESTS): `tools/soundness-duals/const_pointer_*_dual.rs`.
//!
//! Nothing here is proved.

use ay_bindings::Expr;
use rustc_public::mir::alloc::{AllocId, GlobalAlloc};
use rustc_public::mir::mono::{Instance, StaticDef};
use rustc_public::mir::{Body, MirVisitor, visit::Location};
use rustc_public::ty::{Allocation, ConstantKind, MirConst, RigidTy, Ty, TyConstKind, TyKind};

use crate::codegen_ay::types::POINTER_WIDTH;

/// Bytes in one pointer-width word.
pub(in crate::codegen_ay) const PTR_BYTES: usize = (POINTER_WIDTH / 8) as usize;

/// Deepest relocation chain [`reachable_targets`] follows from a body
/// constant (moved from the BMC lane's `materialize_body_global_allocs`).
pub(in crate::codegen_ay) const MAX_PROVENANCE_DEPTH: usize = 8;

/// THE identity key of a relocation target that has an address: a static by
/// its definition, constant memory by its allocation id. Functions and
/// vtables have no key (a function is named by its identity, only at offset 0).
/// Both lanes key their one object table by it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(in crate::codegen_ay) enum TargetKey {
    Static(StaticDef),
    Memory(AllocId),
}

impl TargetKey {
    /// The key of `alloc_id`, or `None` for a function, vtable or type id.
    fn of(alloc_id: AllocId) -> Option<TargetKey> {
        match GlobalAlloc::from(alloc_id) {
            GlobalAlloc::Static(def) => Some(TargetKey::Static(def)),
            GlobalAlloc::Memory(_) => Some(TargetKey::Memory(alloc_id)),
            _ => None,
        }
    }

    /// The BMC lane's symbol spelling of this key (`global_alloc_<key>_addr`),
    /// unchanged from the lane's former string key.
    pub(in crate::codegen_ay) fn symbol_key(&self) -> String {
        use crate::rustc_public_bridge::IndexedVal;
        match self {
            TargetKey::Static(def) => format!("static:{}", def.0.to_index()),
            TargetKey::Memory(alloc_id) => format!("alloc:{}", alloc_id.to_index()),
        }
    }

    /// The static this key names, if it names one.
    pub(in crate::codegen_ay) fn static_def(&self) -> Option<StaticDef> {
        match self {
            TargetKey::Static(def) => Some(*def),
            TargetKey::Memory(_) => None,
        }
    }
}

/// What a relocation's target allocation is.
#[derive(Clone, Debug)]
pub(in crate::codegen_ay) enum ConstTarget {
    Memory,
    Static(StaticDef),
    Function(Instance),
    /// A vtable or a type-id segment: no address this module can name.
    Other,
}

/// A relocation: target allocation plus the offset its bytes carry. The
/// fields are private: the target can be CLASSIFIED ([`ConstPtr::kind`]) or
/// KEYED ([`ConstPtr::key`]), and the only way to an address is
/// [`ConstPtr::address`], which adds the offset.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay) struct ConstPtr {
    target: AllocId,
    offset: u64,
}

impl ConstPtr {
    /// What the target is.
    pub(in crate::codegen_ay) fn kind(&self) -> ConstTarget {
        match GlobalAlloc::from(self.target) {
            GlobalAlloc::Memory(_) => ConstTarget::Memory,
            GlobalAlloc::Static(def) => ConstTarget::Static(def),
            GlobalAlloc::Function(instance) => ConstTarget::Function(instance),
            _ => ConstTarget::Other,
        }
    }

    /// The target's identity key; `None` for a function or vtable.
    pub(in crate::codegen_ay) fn key(&self) -> Option<TargetKey> {
        TargetKey::of(self.target)
    }

    /// The function this pointer names, only when it names it at offset 0.
    pub(in crate::codegen_ay) fn function(&self) -> Option<Instance> {
        match self.kind() {
            ConstTarget::Function(instance) if self.offset == 0 => Some(instance),
            _ => None,
        }
    }

    /// The byte offset the pointer's bytes carry into its target.
    pub(in crate::codegen_ay) fn offset(&self) -> u64 {
        self.offset
    }

    /// `base + offset`, where `base` is the target's ONE address in the lane.
    /// `None` when the offset does not fit the lane's offset field
    /// (`offset_bits`: CHC 32, BMC 64), never a silent truncation.
    pub(in crate::codegen_ay) fn address(&self, base: &Expr, offset_bits: u32) -> Option<Expr> {
        if offset_bits < 64 && self.offset >= (1u64 << offset_bits) {
            return None;
        }
        if self.offset == 0 {
            return Some(base.clone());
        }
        Some(base.clone().bvadd(Expr::bitvec_const(u128::from(self.offset), POINTER_WIDTH)))
    }

    /// This pointer moved by `delta` bytes, when the result stays at a
    /// non-negative offset.
    pub(in crate::codegen_ay) fn moved(&self, delta: i128) -> Option<ConstPtr> {
        let offset = i128::from(self.offset).checked_add(delta)?;
        Some(ConstPtr { target: self.target, offset: u64::try_from(offset).ok()? })
    }
}

/// A read under the slot clause.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay) enum Slot {
    /// No relocation overlaps the read and every byte is initialized.
    Data(u128),
    /// A pointer-width read starting exactly at a relocation.
    Pointer(ConstPtr),
    /// Some byte of the read is uninitialized.
    Uninit,
    /// A relocation overlaps the read without being exactly it.
    PartialPointer,
    /// The read leaves the bytes.
    OutOfBounds,
}

impl Slot {
    /// The data, when the slot is data.
    pub(in crate::codegen_ay) fn data(self) -> Option<u128> {
        match self {
            Slot::Data(value) => Some(value),
            _ => None,
        }
    }
}

/// Read-only views of constant bytes whose ONLY byte accessors obey the slot
/// clause. Composite readers take a `ConstRead`, never an `Allocation`.
pub(in crate::codegen_ay) trait ConstRead {
    /// Number of bytes.
    fn len(&self) -> usize;
    /// `Data` only when no relocation overlaps `[at, at + width/8)`;
    /// `Pointer` only for a pointer-width read starting exactly at a
    /// relocation. `width_bits` is a multiple of 8, at most 128.
    fn read_slot(&self, at: usize, width_bits: u32) -> Slot;
    /// The relocation STARTING at `at`, with the offset its bytes carry.
    fn stored_pointer(&self, at: usize) -> Option<ConstPtr>;
    /// The initialized pointer-width data word at `at` (a length or other
    /// metadata word); `None` when a relocation overlaps it.
    fn stored_word(&self, at: usize) -> Option<u64>;
    /// Owned sub-view `[at, at + len)` with its relocations rebased by −at;
    /// `None` when it leaves the bytes or a relocation straddles an edge.
    fn sub_window(&self, at: usize, len: usize) -> Option<ConstWindow>;
    /// Every relocation, in byte order: its position, and the pointer when
    /// its bytes are all initialized.
    fn relocations(&self) -> Vec<(usize, Option<ConstPtr>)>;
    /// Every relocation, in byte order: its position, and the key of the
    /// target its ENTRY names (`None` for a function, vtable or type id),
    /// whether or not the pointer's offset bytes are initialized. For
    /// classifiers that ask only what a constant may point into (the CHC
    /// untyped-view net 2); a reader that forms an address takes
    /// [`ConstRead::stored_pointer`].
    fn relocation_keys(&self) -> Vec<(usize, Option<TargetKey>)>;
    /// Whether any relocation is present.
    fn has_relocations(&self) -> bool {
        !self.relocations().is_empty()
    }
    /// The bytes' alignment.
    fn align(&self) -> u64;
    /// Whether every byte is initialized data (no relocation, no uninit).
    fn is_plain_data(&self) -> bool {
        !self.has_relocations() && (0..self.len()).all(|at| self.read_slot(at, 8).data().is_some())
    }
    /// The `size`-byte little-endian integer at `at` (size ≤ 16), when it is
    /// data under the slot clause.
    fn read_uint_at(&self, at: usize, size: usize) -> Option<u128> {
        if size == 0 || size > 16 {
            return None;
        }
        self.read_slot(at, (size * 8) as u32).data()
    }
    /// The `size`-byte little-endian signed integer at `at` (size ≤ 16),
    /// sign-extended, when it is data under the slot clause.
    fn read_int_at(&self, at: usize, size: usize) -> Option<i128> {
        let raw = self.read_uint_at(at, size)?;
        let bits = (size * 8) as u32;
        Some(if bits < 128 && raw & (1u128 << (bits - 1)) != 0 {
            (raw | !((1u128 << bits) - 1)) as i128
        } else {
            raw as i128
        })
    }
    /// The `bool` at `at`: data 0 or 1 only (any other byte is not a bool).
    fn read_bool_at(&self, at: usize) -> Option<bool> {
        match self.read_uint_at(at, 1)? {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        }
    }
    /// The `width_bits` little-endian word at `at` with uninitialized bytes
    /// read as 0 — the zeroed static image Kani/CBMC give a static's padding
    /// (`union_transmute`'s oracle needs it). Declines when a relocation
    /// overlaps the read or it leaves the bytes: relocated bytes are never
    /// data, zero-filled or not. (Whether padding may be pinned to 0 is its
    /// own audit item; it is kept exactly as it was.)
    fn read_uint_zero_filled(&self, at: usize, width_bits: u32) -> Option<u128> {
        match self.read_slot(at, width_bits) {
            Slot::Data(value) => Some(value),
            Slot::Uninit => {
                let mut value = 0u128;
                for i in 0..(width_bits / 8) as usize {
                    match self.read_slot(at + i, 8) {
                        Slot::Data(byte) => value |= byte << (i * 8),
                        Slot::Uninit => {}
                        _ => return None,
                    }
                }
                Some(value)
            }
            Slot::Pointer(_) | Slot::PartialPointer | Slot::OutOfBounds => None,
        }
    }
    /// The bytes `[at, at + len)`, when every one is data under the slot
    /// clause.
    fn read_data_bytes(&self, at: usize, len: usize) -> Option<Vec<u8>> {
        (0..len).map(|i| self.read_slot(at.checked_add(i)?, 8).data().map(|b| b as u8)).collect()
    }
    /// Every byte, `None` where uninitialized, for a byte-wise reader that
    /// zero-fills padding (the static image Kani/CBMC give a static). Only
    /// when NO relocation is present: relocated bytes are never data, so a
    /// pointer-bearing image has no byte view at all.
    fn data_image(&self) -> Option<Vec<Option<u8>>> {
        if self.has_relocations() {
            return None;
        }
        Some(
            (0..self.len())
                .map(|at| match self.read_slot(at, 8) {
                    Slot::Data(b) => Some(b as u8),
                    _ => None,
                })
                .collect(),
        )
    }
}

/// A constant's own bytes.
#[derive(Clone, Copy)]
pub(in crate::codegen_ay) struct ConstBytes<'a>(&'a Allocation);

/// An owned, rebased window of a target's bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay) struct ConstWindow(Allocation);

fn alloc_read_slot(alloc: &Allocation, at: usize, width_bits: u32) -> Slot {
    debug_assert!(width_bits % 8 == 0 && width_bits <= 128);
    let width = (width_bits / 8) as usize;
    let Some(end) = at.checked_add(width) else { return Slot::OutOfBounds };
    if end > alloc.bytes.len() || width == 0 {
        return Slot::OutOfBounds;
    }
    for (pos, prov) in &alloc.provenance.ptrs {
        let (pos, pend) = (*pos, *pos + PTR_BYTES);
        if pos < end && pend > at {
            if pos == at && width == PTR_BYTES {
                return match alloc_stored_word_raw(alloc, at) {
                    Some(offset) => Slot::Pointer(ConstPtr { target: prov.0, offset }),
                    None => Slot::PartialPointer,
                };
            }
            return Slot::PartialPointer;
        }
    }
    let mut value = 0u128;
    for (i, byte) in alloc.bytes[at..end].iter().enumerate() {
        let Some(byte) = byte else { return Slot::Uninit };
        value |= u128::from(*byte) << (i * 8);
    }
    Slot::Data(value)
}

/// The initialized little-endian pointer-width word at `at`, whatever
/// provenance covers it (the offset a relocation's own bytes carry).
fn alloc_stored_word_raw(alloc: &Allocation, at: usize) -> Option<u64> {
    let bytes = alloc.bytes.get(at..at.checked_add(PTR_BYTES)?)?;
    bytes.iter().rev().try_fold(0u64, |acc, b| b.map(|b| (acc << 8) | u64::from(b)))
}

fn alloc_stored_pointer(alloc: &Allocation, at: usize) -> Option<ConstPtr> {
    let (_, prov) = alloc.provenance.ptrs.iter().find(|(pos, _)| *pos == at)?;
    Some(ConstPtr { target: prov.0, offset: alloc_stored_word_raw(alloc, at)? })
}

fn alloc_sub_window(alloc: &Allocation, at: usize, len: usize, align: u64) -> Option<ConstWindow> {
    let end = at.checked_add(len)?;
    let bytes = alloc.bytes.get(at..end)?.to_vec();
    let mut ptrs = Vec::new();
    for (pos, prov) in &alloc.provenance.ptrs {
        if *pos >= at && pos + PTR_BYTES <= end {
            ptrs.push((pos - at, *prov));
        } else if *pos < end && pos + PTR_BYTES > at {
            return None;
        }
    }
    Some(ConstWindow(Allocation {
        bytes,
        provenance: rustc_public::ty::ProvenanceMap { ptrs },
        align,
        mutability: alloc.mutability,
    }))
}

fn alloc_relocations(alloc: &Allocation) -> Vec<(usize, Option<ConstPtr>)> {
    alloc
        .provenance
        .ptrs
        .iter()
        .map(|(pos, prov)| {
            (
                *pos,
                alloc_stored_word_raw(alloc, *pos)
                    .map(|offset| ConstPtr { target: prov.0, offset }),
            )
        })
        .collect()
}

macro_rules! impl_const_read {
    ($ty:ty, $alloc:ident => $get:expr) => {
        impl ConstRead for $ty {
            fn len(&self) -> usize {
                let $alloc = self;
                $get.bytes.len()
            }
            fn read_slot(&self, at: usize, width_bits: u32) -> Slot {
                let $alloc = self;
                alloc_read_slot($get, at, width_bits)
            }
            fn stored_pointer(&self, at: usize) -> Option<ConstPtr> {
                let $alloc = self;
                alloc_stored_pointer($get, at)
            }
            fn stored_word(&self, at: usize) -> Option<u64> {
                let $alloc = self;
                let alloc = $get;
                if alloc
                    .provenance
                    .ptrs
                    .iter()
                    .any(|(pos, _)| *pos < at + PTR_BYTES && pos + PTR_BYTES > at)
                {
                    return None;
                }
                alloc_stored_word_raw(alloc, at)
            }
            fn sub_window(&self, at: usize, len: usize) -> Option<ConstWindow> {
                let $alloc = self;
                let alloc = $get;
                let align = if at == 0 {
                    alloc.align
                } else {
                    1u64 << at.trailing_zeros().min(alloc.align.trailing_zeros())
                };
                alloc_sub_window(alloc, at, len, align)
            }
            fn relocations(&self) -> Vec<(usize, Option<ConstPtr>)> {
                let $alloc = self;
                alloc_relocations($get)
            }
            fn relocation_keys(&self) -> Vec<(usize, Option<TargetKey>)> {
                let $alloc = self;
                $get.provenance
                    .ptrs
                    .iter()
                    .map(|(pos, prov)| (*pos, TargetKey::of(prov.0)))
                    .collect()
            }
            fn align(&self) -> u64 {
                let $alloc = self;
                $get.align
            }
        }
    };
}

impl_const_read!(ConstBytes<'_>, this => this.0);
impl_const_read!(ConstWindow, this => &this.0);

impl ConstWindow {
    /// This window with its alignment set to `align` (a pointee's ABI
    /// alignment when the window is a pointee).
    pub(in crate::codegen_ay) fn with_align(mut self, align: u64) -> ConstWindow {
        self.0.align = align;
        self
    }
}

/// THE entry point for a MIR constant's own bytes.
pub(in crate::codegen_ay) fn const_bytes(c: &MirConst) -> Option<ConstBytes<'_>> {
    match c.kind() {
        ConstantKind::Allocated(alloc) => Some(ConstBytes(alloc)),
        ConstantKind::Ty(ty_const) => match ty_const.kind() {
            TyConstKind::Value(_, alloc) => Some(ConstBytes(alloc)),
            _ => None,
        },
        _ => None,
    }
}

/// A scalar constant's whole bytes (at most 16) as a little-endian unsigned
/// integer, when they are data under the slot clause. The integer readers
/// of every lane take a constant through here, never through its
/// allocation.
pub(in crate::codegen_ay) fn const_uint(c: &MirConst) -> Option<u128> {
    let bytes = const_bytes(c)?;
    bytes.read_uint_at(0, bytes.len())
}

/// [`const_uint`], sign-extended from the constant's width.
pub(in crate::codegen_ay) fn const_int(c: &MirConst) -> Option<i128> {
    let bytes = const_bytes(c)?;
    bytes.read_int_at(0, bytes.len())
}

/// A one-byte `bool` constant: data 0 or 1.
pub(in crate::codegen_ay) fn const_bool(c: &MirConst) -> Option<bool> {
    let bytes = const_bytes(c)?;
    if bytes.len() != 1 {
        return None;
    }
    bytes.read_bool_at(0)
}

/// A pointer-typed constant's own value: the data pointer, and the metadata
/// word beside it when the pointee is `[T]` / `str` (its length).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay) struct ConstRef {
    pub(in crate::codegen_ay) ptr: ConstPtr,
    pub(in crate::codegen_ay) metadata: Option<u64>,
}

/// Whether `pointee` is a slice-like DST whose metadata is a length word.
pub(in crate::codegen_ay) fn pointee_has_len_metadata(pointee: Ty) -> bool {
    matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Slice(_) | RigidTy::Str))
}

/// The pointer stored at `at` in `bytes`, read as a pointer to `pointee`:
/// the data pointer, plus the length word at `at + PTR_BYTES` for a
/// `[T]` / `str` pointee. `None` when no relocation starts at `at`, or a
/// length word is not initialized data.
pub(in crate::codegen_ay) fn const_ref(
    bytes: &dyn ConstRead,
    at: usize,
    pointee: Ty,
) -> Option<ConstRef> {
    let ptr = bytes.stored_pointer(at)?;
    let metadata = if pointee_has_len_metadata(pointee) {
        Some(bytes.stored_word(at.checked_add(PTR_BYTES)?)?)
    } else {
        None
    };
    Some(ConstRef { ptr, metadata })
}

/// The bytes a pointee of type `pointee` occupies: `size_of` for a sized
/// pointee, `len × size_of(elem)` for `[elem]` / `str`. `None` for any other
/// unsized pointee (a `dyn` or a slice-tailed struct), which fails closed.
pub(in crate::codegen_ay) fn pointee_extent(pointee: Ty, metadata: Option<u64>) -> Option<u64> {
    match pointee.kind() {
        TyKind::RigidTy(RigidTy::Str) => metadata,
        TyKind::RigidTy(RigidTy::Slice(elem)) => {
            let size = elem.layout().ok()?.shape().size.bytes() as u64;
            metadata?.checked_mul(size)
        }
        _ => {
            let shape = pointee.layout().ok()?.shape();
            shape.is_sized().then(|| shape.size.bytes() as u64)
        }
    }
}

/// The ABI alignment of a pointee (of its element for `[T]`, 1 for `str`).
fn pointee_align(pointee: Ty) -> Option<u64> {
    match pointee.kind() {
        TyKind::RigidTy(RigidTy::Str) => Some(1),
        TyKind::RigidTy(RigidTy::Slice(elem)) => Some(elem.layout().ok()?.shape().abi_align),
        _ => Some(pointee.layout().ok()?.shape().abi_align),
    }
}

/// The window `r` names in `target`: `[k, k + extent)`, relocations rebased.
pub(in crate::codegen_ay) fn pointee_window(
    target: &dyn ConstRead,
    r: &ConstRef,
    pointee: Ty,
) -> Option<ConstWindow> {
    let start = usize::try_from(r.ptr.offset).ok()?;
    let extent = usize::try_from(pointee_extent(pointee, r.metadata)?).ok()?;
    Some(target.sub_window(start, extent)?.with_align(pointee_align(pointee)?))
}

/// THE reader: the pointer stored at `at` in `bytes` → its target, only when
/// the target's bytes are fixed for the run → the window at the pointer's
/// offset. A nested hop is `fixed_pointee(tcx, &window, at, inner)` again.
pub(in crate::codegen_ay) fn fixed_pointee(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    bytes: &dyn ConstRead,
    at: usize,
    pointee: Ty,
) -> Option<(ConstRef, ConstWindow)> {
    let r = const_ref(bytes, at, pointee)?;
    let (target, fixed) = target_bytes(tcx, &r.ptr.key()?)?;
    if fixed != Fixedness::Fixed {
        return None;
    }
    let window = pointee_window(&target, &r, pointee)?;
    Some((r, window))
}

/// The window of a pointer derived from `r` by a known `delta_bytes`, read
/// at type `pointee` (sized): a RE-DECODE at `k + delta`, never a copy of the
/// window `r` itself names.
pub(in crate::codegen_ay) fn fixed_pointee_at(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    r: &ConstRef,
    delta_bytes: i128,
    pointee: Ty,
) -> Option<ConstWindow> {
    let moved = ConstRef { ptr: r.ptr.moved(delta_bytes)?, metadata: None };
    let (target, fixed) = target_bytes(tcx, &moved.ptr.key()?)?;
    if fixed != Fixedness::Fixed {
        return None;
    }
    pointee_window(&target, &moved, pointee)
}

/// Whether a target's bytes are fixed for the whole run.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay) enum Fixedness {
    /// Constant memory, or a static that is not `mut`, not foreign, `Freeze`
    /// and evaluable: its bytes may be decoded into values.
    Fixed,
    /// A `static mut` or an interior-mutable static: its bytes are the
    /// INITIAL image only; a read observes the live state.
    Live,
}

/// A static's initializer, when rustc can evaluate it. A FOREIGN static
/// (`extern "C" { static X: T; }`) has no initializer body and
/// `eval_initializer()` raises a rustc `span_bug` — an abort, not an `Err`
/// (kani/Static/unsafe_extern_static_uninitialized.rs crashed the compiler) —
/// and a still-generic type cannot be evaluated. Both are declined.
fn evaluable_static_initializer(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    static_def: StaticDef,
) -> Option<Allocation> {
    use rustc_public::CrateDef;
    let def_id = rustc_public::rustc_internal::internal(tcx, static_def.def_id());
    if tcx.is_foreign_item(def_id) {
        return None;
    }
    // A NESTED (anonymous) static — the `&mut 42` inside
    // `static mut FOO: &mut u32 = &mut 42` — is a synthetic definition:
    // `type_of` on it is a rustc `span_bug` (kani/Static/anon_static.rs crashed
    // the compiler). It is never generic, and its initializer is the allocation
    // rustc interned for it, so skip only the type query.
    if !crate::kani_middle::is_anon_static(tcx, static_def.def_id())
        && super::mono_ty::has_unresolved_params(static_def.ty())
    {
        return None;
    }
    static_def.eval_initializer().ok()
}

/// Whether a static's bytes are fixed: not `static mut`, and a `Freeze` type
/// (`UnsafeCell`, and so `Cell`/`RefCell`/atomics, can be written through an
/// `&`). An anonymous nested static has no type query; its interned
/// allocation's mutability says whether it can change.
fn static_fixedness(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    static_def: StaticDef,
    init: &Allocation,
) -> Fixedness {
    use rustc_public::CrateDef;
    let def_id = rustc_public::rustc_internal::internal(tcx, static_def.def_id());
    if crate::kani_middle::is_anon_static(tcx, static_def.def_id()) {
        return if matches!(init.mutability, rustc_public::mir::Mutability::Not) {
            Fixedness::Fixed
        } else {
            Fixedness::Live
        };
    }
    if tcx.is_mutable_static(def_id) {
        return Fixedness::Live;
    }
    let internal_ty = rustc_public::rustc_internal::internal(tcx, static_def.ty());
    if !internal_ty.is_freeze(tcx, rustc_middle::ty::TypingEnv::fully_monomorphized()) {
        return Fixedness::Live;
    }
    Fixedness::Fixed
}

/// The whole bytes of the target `key` names, and whether they are fixed.
/// `None` for a static whose initializer cannot be evaluated (foreign,
/// generic).
///
/// Whole-target bytes are for the object tables (`statement::global_alloc`,
/// `chc::decl::global_objects`, and the CHC static seeding in
/// `chc::decl::codegen_decl_static*`), which seed whole objects and a
/// static's own state at offset 0 with its own type, and for the CHC
/// untyped-view net 2 (`chc::stmt::codegen_stmt_store::untyped_view_scan`),
/// which classifies their relocations and checks an already-seeded native
/// byte view at an exact immutable allocation offset; every other reader
/// goes through [`fixed_pointee`]. The lint in `test_const_pointer_single_rule.rs`
/// keeps rustc's representation out of every caller; it does not hold this
/// list of call sites, which is code-read.
pub(in crate::codegen_ay) fn target_bytes(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    key: &TargetKey,
) -> Option<(ConstWindow, Fixedness)> {
    match key {
        TargetKey::Memory(alloc_id) => match GlobalAlloc::from(*alloc_id) {
            GlobalAlloc::Memory(alloc) => Some((ConstWindow(alloc), Fixedness::Fixed)),
            _ => None,
        },
        TargetKey::Static(def) => {
            let init = evaluable_static_initializer(tcx, *def)?;
            let fixed = static_fixedness(tcx, *def, &init);
            Some((ConstWindow(init), fixed))
        }
    }
}

/// One target of [`reachable_targets`].
pub(in crate::codegen_ay) struct Reached {
    pub(in crate::codegen_ay) key: TargetKey,
    pub(in crate::codegen_ay) bytes: Option<(ConstWindow, Fixedness)>,
}

/// The transitive closure of relocations from a body's constants.
pub(in crate::codegen_ay) struct Reachable {
    /// In discovery order (a LIFO walk, as the BMC lane always walked).
    pub(in crate::codegen_ay) targets: Vec<Reached>,
    /// A target past [`MAX_PROVENANCE_DEPTH`] was not walked into.
    pub(in crate::codegen_ay) depth_exceeded: bool,
}

struct BodyConsts<'f> {
    admit: &'f dyn Fn(Ty) -> bool,
    found: Vec<ConstWindow>,
}

impl MirVisitor for BodyConsts<'_> {
    fn visit_mir_const(&mut self, constant: &MirConst, location: Location) {
        if (self.admit)(constant.ty())
            && let Some(bytes) = const_bytes(constant)
        {
            self.found.push(ConstWindow(bytes.0.clone()));
        }
        self.super_mir_const(constant, location);
    }
}

/// Every constant `body` spells in the basic blocks `keep` selects (indexed
/// like `body.blocks`; a missing index is kept), with its type and its own
/// bytes (owned), for the lanes' read-set scans — leaving out the constants
/// passed to a call whose callee `args_unread` (the lane's knowledge of its
/// own models) says never reads through its arguments: a message-only hook
/// such as `kani::assert`. Such a constant is a value nothing dereferences.
pub(in crate::codegen_ay) fn body_constants_read(
    body: &Body,
    keep: &[bool],
    args_unread: &dyn Fn(&rustc_public::mir::Operand) -> bool,
) -> Vec<(ConstWindow, Ty)> {
    struct Read<'f> {
        found: Vec<(ConstWindow, Ty)>,
        args_unread: &'f dyn Fn(&rustc_public::mir::Operand) -> bool,
        block: usize,
    }
    impl MirVisitor for Read<'_> {
        fn visit_mir_const(&mut self, constant: &MirConst, location: Location) {
            if let Some(bytes) = const_bytes(constant) {
                if bytes.has_relocations() {
                    tracing::debug!(
                        block = self.block,
                        ty = ?constant.ty(),
                        len = bytes.len(),
                        "read set: a constant whose pointers the body may read"
                    );
                }
                self.found.push((ConstWindow(bytes.0.clone()), constant.ty()));
            }
            self.super_mir_const(constant, location);
        }
        fn visit_terminator(&mut self, term: &rustc_public::mir::Terminator, location: Location) {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &term.kind
                && (self.args_unread)(func)
            {
                return;
            }
            self.super_terminator(term, location);
        }
    }
    let mut read = Read { found: Vec::new(), args_unread, block: 0 };
    for (idx, block) in body.blocks.iter().enumerate() {
        if keep.get(idx).copied().unwrap_or(true) {
            read.block = idx;
            read.visit_basic_block(block);
        }
    }
    read.found
}

/// The targets `body`'s constants reach: every relocation of every admitted
/// constant (`admit` is the lane's filter on the constant's type), then every
/// relocation of every reached target's bytes, to depth
/// [`MAX_PROVENANCE_DEPTH`]. Moved from the BMC lane's
/// `materialize_body_global_allocs` (same LIFO walk, same order).
pub(in crate::codegen_ay) fn reachable_targets(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    body: &Body,
    admit: impl Fn(Ty) -> bool,
) -> Reachable {
    let mut visitor = BodyConsts { admit: &admit, found: Vec::new() };
    visitor.visit_body(body);
    let mut seen: std::collections::HashSet<TargetKey> = std::collections::HashSet::new();
    let mut out = Reachable { targets: Vec::new(), depth_exceeded: false };
    let mut work: Vec<(ConstWindow, usize)> = visitor.found.into_iter().map(|a| (a, 0)).collect();
    while let Some((bytes, depth)) = work.pop() {
        // The relocation ENTRY names the target, whether or not the pointer's
        // offset bytes are all initialized.
        for (_, prov) in &bytes.0.provenance.ptrs {
            let Some(key) = TargetKey::of(prov.0) else { continue };
            if !seen.insert(key) {
                continue;
            }
            let target = target_bytes(tcx, &key);
            if let Some((window, _)) = &target {
                if depth + 1 < MAX_PROVENANCE_DEPTH {
                    work.push((window.clone(), depth + 1));
                } else if window.has_relocations() {
                    out.depth_exceeded = true;
                }
            }
            out.targets.push(Reached { key, bytes: target });
        }
    }
    out
}
