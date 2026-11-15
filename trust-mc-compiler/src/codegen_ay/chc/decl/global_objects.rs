// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The CHC lane's ONE object table for global allocations (constant memory
//! and statics), keyed by `shared::const_pointer::TargetKey`, with ONE mint
//! function.
//!
//! The rule it implements is stated once, in `shared::const_pointer`: a
//! constant pointer denotes `base(T) + k`, where `base(T)` is the ONE address
//! the lane gives its target T for the whole harness. In the CHC lane an
//! address is a split pointer `concat(obj_id:32, offset:32)`, so `base(T)` is
//! `concat(obj_id(T), 0)` and the pointer is that plus its offset k.
//!
//! Before this table there were two AllocId-keyed maps with two mint sites
//! (`static_address_exprs`, minted by the static collector and again by the
//! pointer-static resolver; and `promoted_const_alloc_addresses`, minted per
//! ASSIGNMENT of a constant), plus the shared fallback object 1 for every
//! unregistered constant. One allocation got several objects (`ptr::eq(E0,
//! E1)` for two constants into one array PROVED), and one static got two
//! (`*PX = 7; X == 1` PROVED). The key is now the identity, and
//! [`ChcCtx::mint_object`] cannot mint a key twice.
//!
//! Objects are minted before translation (`collect_global_objects`, and
//! `register_callee_body_consts` for an inlined callee's body), from the
//! shared transitive walk `const_pointer::reachable_targets`. A target that
//! was never minted has no address: [`ChcCtx::const_ptr_address`] returns
//! `None` (a recorded constant-translation drop), never another object.

use std::sync::Arc;

use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, Sort};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use tracing::debug;

use crate::codegen_ay::provenance::Loc;
use crate::codegen_ay::shared::const_pointer::{
    self, ConstPtr, ConstRead, ConstTarget, Fixedness, TargetKey,
};

use super::ChcCtx;
use super::codegen_types::CodegenTypes;

/// One global allocation's object in the CHC lane.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) struct GlobalObject {
    /// The split-pointer object id.
    pub(in crate::codegen_ay::chc) obj_id: u32,
    /// The allocation's byte length, when its bytes are known.
    pub(in crate::codegen_ay::chc) size: Option<u64>,
    /// Whether its bytes are fixed for the run (`None`: bytes unknown, a
    /// foreign or generic static).
    pub(in crate::codegen_ay::chc) fixed: Option<Fixedness>,
}

/// The split-pointer base address of an object id: `concat(obj_id, 0)`.
pub(in crate::codegen_ay::chc) fn object_base_for(obj_id: u32) -> Expr {
    Expr::bitvec_const(i128::from(obj_id), 32).concat(Expr::bitvec_const(0i128, 32))
}

/// The CHC offset field is 32 bits wide (`concat(obj_id:32, offset:32)`).
pub(in crate::codegen_ay::chc) const CHC_OFFSET_BITS: u32 = 32;

/// Largest fixed object seeded cell by cell (the BMC lane's bound).
pub(in crate::codegen_ay::chc) const MAX_SEEDED_OBJECT_BYTES: usize = 4096;

/// Sound-fallback reason: a FIXED object a constant pointer reaches that is
/// larger than [`MAX_SEEDED_OBJECT_BYTES`], so its cells stay free. Free cells
/// admit every value the constant really has, so a proof over them is a proof;
/// a counterexample may rest on a value the object never holds, so it is
/// recorded and never certified (`codegen_ctx::fallback_soundness`).
pub(in crate::codegen_ay::chc) const CONST_OBJECT_UNSEEDED: &str = "const_object_unseeded";

/// Where a decoded window's memory seeds land: its target's object and the
/// window's byte offset in that object. Every `const_ref_memory_inits` entry
/// is object-relative (`site.at(offset_in_window)`), so a window at offset k
/// seeds `base + k + j`, never `base + j`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) struct InitSite {
    pub(in crate::codegen_ay::chc) obj_id: u32,
    pub(in crate::codegen_ay::chc) base: u64,
}

impl InitSite {
    /// The object-relative offset of `offset_in_window`.
    pub(in crate::codegen_ay::chc) fn at(&self, offset_in_window: u64) -> u64 {
        self.base + offset_in_window
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// THE mint (D1): the object of `key`, minted on first use and never
    /// again. Idempotent per key, so no caller can give one target two
    /// objects.
    pub(in crate::codegen_ay::chc) fn mint_object(&mut self, key: TargetKey) -> Option<u32> {
        if let Some(object) = self.ref_resolution.global_objects.get(&key) {
            return Some(object.obj_id);
        }
        let obj_id = self.heap_state.next_alloc_id()?;
        let bytes = const_pointer::target_bytes(self.tcx, &key);
        let object = GlobalObject {
            obj_id,
            size: bytes.as_ref().map(|(window, _)| window.len() as u64),
            fixed: bytes.as_ref().map(|(_, fixed)| *fixed),
        };
        debug!(?key, obj_id, ?object.size, ?object.fixed, "CHC: minted global object");
        self.ref_resolution.global_objects.insert(key, object);
        Some(obj_id)
    }

    /// The object of `key`, if minted.
    pub(in crate::codegen_ay::chc) fn global_object(
        &self,
        key: &TargetKey,
    ) -> Option<GlobalObject> {
        self.ref_resolution.global_objects.get(key).copied()
    }

    /// THE lookup: the base address `concat(obj_id, 0)` of `key`'s object.
    pub(in crate::codegen_ay::chc) fn object_base(&self, key: &TargetKey) -> Option<Loc> {
        self.global_object(key).map(|object| Loc::of_address(object_base_for(object.obj_id)))
    }

    /// The address a constant pointer denotes: its target's object base plus
    /// the offset its bytes carry; a function's identity only at offset 0.
    /// `None` when the target was never minted, is a vtable, or the offset
    /// does not fit the 32-bit offset field.
    pub(in crate::codegen_ay::chc) fn const_ptr_address(&self, ptr: &ConstPtr) -> Option<Loc> {
        if let ConstTarget::Function(_) = ptr.kind() {
            ptr.function()?;
            return Self::fn_ptr_identity_of_const_ptr(ptr);
        }
        let base = self.object_base(&ptr.key()?)?;
        Some(Loc::of_address(ptr.address(base.as_expr(), CHC_OFFSET_BITS)?))
    }

    /// The identity of the function a constant pointer names (at offset 0):
    /// the same value a reification of that instance mints
    /// (`crate::codegen_ay::fn_ptr_identity::fn_ptr_identity_value`), so a fn
    /// pointer a constant holds compares equal to the same function reified in
    /// code. A function's identity IS its address in this encoding.
    pub(in crate::codegen_ay::chc) fn fn_ptr_identity_of_const_ptr(ptr: &ConstPtr) -> Option<Loc> {
        let instance = ptr.function()?;
        let id = crate::codegen_ay::fn_ptr_identity::fn_ptr_identity_of_instance(&instance);
        Some(Loc::of_address(Expr::bitvec_const(
            u128::from(id),
            crate::codegen_ay::types::POINTER_WIDTH,
        )))
    }

    /// Whether `obj_id` names a CONSTANT-MEMORY object (a promoted constant,
    /// string or byte-string literal, or any other allocation const-eval
    /// interned), as opposed to a static, heap or stack object.
    pub(in crate::codegen_ay::chc) fn is_const_memory_obj_id(&self, obj_id: u32) -> bool {
        self.ref_resolution
            .global_objects
            .iter()
            .any(|(key, object)| matches!(key, TargetKey::Memory(_)) && object.obj_id == obj_id)
    }

    /// The byte length of the constant-memory object `obj_id` (D3: the
    /// object's extent is its allocation's).
    pub(in crate::codegen_ay::chc) fn const_memory_object_size(&self, obj_id: u32) -> Option<u64> {
        self.ref_resolution.global_objects.iter().find_map(|(key, object)| {
            (matches!(key, TargetKey::Memory(_)) && object.obj_id == obj_id)
                .then_some(object.size)
                .flatten()
        })
    }

    /// DECL pass (D1): mint an object for every target the body's constants
    /// reach, transitively through every reached target's bytes. Runs before
    /// the static collector and before Pass 4, so every constant pointer the
    /// harness body names has its one address before translation.
    pub(in crate::codegen_ay::chc) fn collect_global_objects(&mut self) {
        let body = self.body;
        self.mint_reachable_objects(body);
        debug!(count = self.ref_resolution.global_objects.len(), "CHC: collected global objects");
    }

    /// The same walk over an inlined callee's body.
    pub(in crate::codegen_ay::chc) fn register_callee_body_consts(
        &mut self,
        callee_body: &rustc_public::mir::Body,
    ) {
        self.mint_reachable_objects(callee_body);
        self.register_callee_body_statics(callee_body);
    }

    /// Record that the harness reads the object `key` names at type `ty` (the
    /// pointee type of a constant pointer into it, or of a pointer derived from
    /// one). The fixed objects are then seeded WHOLE at every such type
    /// ([`Self::seed_global_objects`], D2).
    ///
    /// A read noted after the seeding closed (an inlined callee's constant the
    /// translation discovers, a decoder that runs during translation) can no
    /// longer be seeded — the entry rule is already emitted — so a FIXED
    /// object read that way records [`CONST_OBJECT_UNSEEDED`]: its cells stay
    /// free, and no counterexample through them is certified.
    pub(in crate::codegen_ay::chc) fn note_object_read(&mut self, key: TargetKey, ty: Ty) {
        let reads = &mut self.ref_resolution.object_read_types;
        let new = match reads.iter_mut().find(|(k, _)| *k == key) {
            Some((_, types)) => {
                if types.contains(&ty) {
                    false
                } else {
                    types.push(ty);
                    true
                }
            }
            None => {
                reads.push((key, vec![ty]));
                true
            }
        };
        if new
            && self.ref_resolution.object_seeding_closed
            && self.global_object(&key).is_some_and(|o| o.fixed == Some(Fixedness::Fixed))
            && !Self::seed_types_for(ty).into_iter().all(|t| {
                self.global_object(&key).is_some_and(|o| {
                    self.ref_resolution.seeded_object_types.contains(&(o.obj_id, t))
                })
            })
        {
            debug!(?key, ?ty, "CHC: fixed object read noted after seeding closed — fail closed");
            self.record_sound_fallback_reason(CONST_OBJECT_UNSEEDED);
        }
    }

    /// Record that the harness dereferences SOME pointer at type `ty` (a deref
    /// in its body or in a pre-scanned callee). A pointer into a fixed object
    /// can reach such a deref by a path no constant names — a cast to another
    /// pointee type (`E as *const u32 as *const u8`), a byte offset, a callee
    /// — so every fixed object the harness reads is seeded at `ty` too (D2:
    /// "at every type the harness reads through a pointer into the object").
    /// After the seeding closed, a new type that a fixed object in the read set
    /// is not seeded at records [`CONST_OBJECT_UNSEEDED`].
    pub(in crate::codegen_ay::chc) fn note_extra_read_type(&mut self, ty: Ty) {
        if self.ref_resolution.extra_read_types.contains(&ty) {
            return;
        }
        self.ref_resolution.extra_read_types.push(ty);
        if !self.ref_resolution.object_seeding_closed {
            return;
        }
        let seed_tys = Self::seed_types_for(ty);
        let unseeded = self.ref_resolution.object_read_types.iter().any(|(key, _)| {
            self.global_object(key).is_some_and(|o| {
                o.fixed == Some(Fixedness::Fixed)
                    && seed_tys
                        .iter()
                        .any(|t| !self.ref_resolution.seeded_object_types.contains(&(o.obj_id, *t)))
            })
        });
        if unseeded {
            debug!(?ty, "CHC: deref type noted after seeding closed — fail closed");
            self.record_sound_fallback_reason(CONST_OBJECT_UNSEEDED);
        }
    }

    /// Close the seeding (D2): from here on the entry rule is emitted, so a
    /// read that would need a seed it cannot get fails closed instead.
    pub(in crate::codegen_ay::chc) fn close_object_seeding(&mut self) {
        if !self.ref_resolution.object_seeding_closed {
            let byte_key = Self::type_key_for_ty(Ty::unsigned_ty(rustc_public::ty::UintTy::U8));
            let byte_array_registered = self
                .heap_state
                .type_arrays
                .get(&*byte_key)
                .is_some_and(|(_, sort)| sort == &Sort::bitvec(8));
            let mut byte_seeds = std::collections::HashMap::new();
            if byte_array_registered {
                let sort = Sort::bitvec(8);
                for (key, cell_sort, value, obj, at) in &self.ref_resolution.const_ref_memory_inits
                {
                    if &**key != byte_key.as_ref() {
                        continue;
                    }
                    let seed = byte_seeds.entry((*obj, *at)).or_insert_with(|| Some(value.clone()));
                    if cell_sort != &sort || value.sort() != &sort || seed.as_ref() != Some(value) {
                        *seed = None;
                    }
                }
            }
            self.ref_resolution.const_ref_entry_byte_seeds = byte_seeds;
        }
        self.ref_resolution.object_seeding_closed = true;
    }

    /// [`Self::note_object_read`] from a `&self` decoder (a pointer found
    /// inside a window names another object read at its pointee type); drained
    /// by Pass 4 and by [`Self::seed_global_objects`].
    pub(in crate::codegen_ay::chc) fn note_object_read_deferred(&self, key: TargetKey, ty: Ty) {
        self.ref_resolution.pending_object_reads.borrow_mut().push((key, ty));
    }

    /// Drop the deferred reads (those of a constant only a panic-only block
    /// names, `collect_const_ref_values`).
    pub(in crate::codegen_ay::chc) fn discard_deferred_object_reads(&self) {
        self.ref_resolution.pending_object_reads.borrow_mut().clear();
    }

    /// Move the deferred reads into the read set; whether any was new.
    pub(in crate::codegen_ay::chc) fn drain_deferred_object_reads(&mut self) -> bool {
        let pending: Vec<(TargetKey, Ty)> =
            std::mem::take(&mut *self.ref_resolution.pending_object_reads.borrow_mut());
        let mut any = false;
        for (key, ty) in pending {
            let before =
                self.ref_resolution.object_read_types.iter().map(|(_, t)| t.len()).sum::<usize>()
                    + self.ref_resolution.object_read_types.len();
            self.note_object_read(key, ty);
            let after =
                self.ref_resolution.object_read_types.iter().map(|(_, t)| t.len()).sum::<usize>()
                    + self.ref_resolution.object_read_types.len();
            any |= after != before;
        }
        any
    }

    /// D2: seed every FIXED object the harness reads through a constant
    /// pointer, WHOLE: for each type Q it is read at (and Q's element type for
    /// an array, slice or `str`), every Q-aligned offset j whose window decodes
    /// as Q under the slot clause gets its typed-memory seed at `base + j`.
    ///
    /// Before this, only the window a constant named was seeded, so a read
    /// through `E.add(1)` or `E.sub(1)` read a FREE cell and its counterexample
    /// was certified (`safe_forward_past_pointee`, `safe_offset0_arith`).
    ///
    /// A cell that does not decode (uninitialized, a partial pointer, an
    /// invalid `bool` / `char` / tag) stays free: reading it is UB or
    /// unconstrained. An object over [`MAX_SEEDED_OBJECT_BYTES`] is left
    /// unseeded and recorded ([`CONST_OBJECT_UNSEEDED`]). Idempotent: each
    /// (object, type) pair is seeded once, so the pass can re-run after late
    /// declaration passes.
    pub(in crate::codegen_ay::chc) fn seed_global_objects(&mut self) {
        // A seeded window can hold a pointer to another fixed object, which is
        // then read at ITS pointee type: iterate to the fixpoint (bounded by
        // the reached targets times their types).
        self.drain_deferred_object_reads();
        loop {
            self.seed_noted_object_reads();
            if !self.drain_deferred_object_reads() {
                break;
            }
        }
    }

    fn seed_noted_object_reads(&mut self) {
        let reads = self.ref_resolution.object_read_types.clone();
        let extra = self.ref_resolution.extra_read_types.clone();
        for (key, noted) in reads {
            let Some(object) = self.global_object(&key) else { continue };
            // The type keys a registered static's typed-memory MIRROR already
            // seeds (its own type, decomposed into fields and elements): two
            // seeds of one cell in one key could disagree in encoding, so those
            // keys stay the mirror's alone.
            let mut mirror_keys: Option<std::collections::HashSet<Arc<str>>> = None;
            if let Some(def) = key.static_def() {
                if self.ref_resolution.registered_static_memory.contains(&def) {
                    // A static the static collector registered keeps its own
                    // state variable and memory mirror. Only a FIXED one is
                    // seeded here, and only at the extra read types its mirror
                    // does not cover (`FS as *const u8`).
                    if object.fixed != Some(Fixedness::Fixed) {
                        continue;
                    }
                    mirror_keys = Some(self.static_mirror_type_keys(object.obj_id));
                } else {
                    // A static reached only through another target's bytes (N6:
                    // `RC` behind `RP`) is seeded here with its INITIAL image —
                    // the entry state of its memory, which is its only
                    // representation — except in a contract CHECK harness,
                    // where a live static must stay havoc (P2-S1).
                    if self.contract_static_havoc && object.fixed != Some(Fixedness::Fixed) {
                        continue;
                    }
                    self.ref_resolution.registered_static_memory.insert(def);
                    // Its layout record: the static's exact extent and alignment.
                    if let Some((target, _)) = const_pointer::target_bytes(self.tcx, &key)
                        && let Ok(size) = u32::try_from(target.len())
                    {
                        self.ref_resolution.static_alloc_sizes.push((
                            object.obj_id,
                            size,
                            target.align(),
                        ));
                    }
                }
            } else if object.fixed != Some(Fixedness::Fixed) {
                continue;
            }
            let Some((target, _)) = const_pointer::target_bytes(self.tcx, &key) else { continue };
            // A live static (N6, entry image only) is seeded at the types it is
            // noted at; a FIXED object at every type the harness reads (D2).
            let mut types = noted;
            if object.fixed == Some(Fixedness::Fixed) {
                for ty in &extra {
                    if !types.contains(ty) {
                        types.push(*ty);
                    }
                }
            }
            for ty in types {
                for seed_ty in Self::seed_types_for(ty) {
                    if !self.ref_resolution.seeded_object_types.insert((object.obj_id, seed_ty)) {
                        continue;
                    }
                    if let Some(keys) = &mirror_keys
                        && keys.contains(&*self.type_key_for_body_ty(seed_ty))
                    {
                        continue;
                    }
                    if target.len() > MAX_SEEDED_OBJECT_BYTES {
                        self.record_sound_fallback_reason(CONST_OBJECT_UNSEEDED);
                        continue;
                    }
                    self.seed_object_at_type(&target, object.obj_id, seed_ty);
                }
            }
        }
    }

    /// The typed-memory keys the static mirror (`static_memory_inits`) seeds
    /// in the object `obj_id`.
    fn static_mirror_type_keys(&self, obj_id: u32) -> std::collections::HashSet<Arc<str>> {
        self.ref_resolution
            .static_memory_inits
            .iter()
            .filter(|(_, _, _, addr)| {
                Self::try_extract_constant_addr(addr).is_some_and(|(obj, _)| obj == obj_id)
            })
            .map(|(key, _, _, _)| Arc::clone(key))
            .collect()
    }

    /// The types a read at `ty` needs seeded: `ty` itself when sized, and the
    /// element type of an array, slice or `str`.
    fn seed_types_for(ty: Ty) -> Vec<Ty> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Str) => {
                vec![Ty::unsigned_ty(rustc_public::ty::UintTy::U8)]
            }
            TyKind::RigidTy(RigidTy::Slice(elem)) => vec![elem],
            TyKind::RigidTy(RigidTy::Array(elem, _)) => vec![ty, elem],
            _ => vec![ty],
        }
    }

    /// Seed the object `obj_id` (bytes `target`) at every `ty`-aligned offset
    /// whose window decodes as `ty`.
    fn seed_object_at_type(&mut self, target: &dyn ConstRead, obj_id: u32, ty: Ty) {
        let Some(shape) = ty.layout().ok().map(|l| l.shape()) else { return };
        if !shape.is_sized() {
            return;
        }
        let size = shape.size.bytes();
        let align = (shape.abi_align as usize).max(1);
        if size == 0 || size > target.len() {
            return;
        }
        let mut inits: Vec<(Arc<str>, Sort, Expr, u32, u64)> = Vec::new();
        let mut at = 0usize;
        while at + size <= target.len() {
            if let Some(window) = target.sub_window(at, size) {
                let site = InitSite { obj_id, base: at as u64 };
                let mut cell_inits = Vec::new();
                if self.decode_window(&window, ty, &mut cell_inits, site).is_some() {
                    inits.extend(cell_inits);
                }
                // A pointer inside the seeded cell names another object read
                // at ITS pointee type (`NH.r`, an array of references).
                self.note_pointer_slots(&window, ty, 0);
            }
            at += align;
        }
        self.push_const_memory_inits(inits);
    }

    /// Append memory seeds, keeping one entry per (type, object, offset).
    pub(in crate::codegen_ay::chc) fn push_const_memory_inits(
        &mut self,
        inits: Vec<(Arc<str>, Sort, Expr, u32, u64)>,
    ) {
        for init in inits {
            let key = (Arc::clone(&init.0), init.1.clone(), init.3, init.4);
            if self.ref_resolution.object_seeding_closed
                && !self.ref_resolution.seeded_cells.contains(&key)
            {
                // The entry rule is final. Replaying a new late cell in bb0
                // would not make it an entry constraint, so leave it free.
                self.record_sound_fallback_reason(CONST_OBJECT_UNSEEDED);
                continue;
            }
            if self.ref_resolution.seeded_cells.insert(key) {
                self.ref_resolution.const_ref_memory_inits.push(init);
            }
        }
    }

    /// THE decoded value of the FIXED pointee window the pointer stored at
    /// `at` in `bytes` names, read at `pointee`: one expression per window
    /// (`window_values`), so every pointer-typed static naming it denotes the
    /// same value. `None` when the pointer's target is not fixed or the window
    /// does not decode.
    pub(in crate::codegen_ay::chc) fn fixed_window_value(
        &mut self,
        bytes: &dyn ConstRead,
        at: usize,
        pointee: Ty,
    ) -> Option<(const_pointer::ConstRef, Expr)> {
        let (r, window) = const_pointer::fixed_pointee(self.tcx, bytes, at, pointee)?;
        let cache_key = (r.ptr.key()?, r.ptr.offset(), r.metadata, pointee);
        if let Some(value) = self.ref_resolution.window_values.get(&cache_key) {
            return Some((r, value.clone()));
        }
        let mut scratch = Vec::new();
        let value =
            self.decode_window(&window, pointee, &mut scratch, InitSite { obj_id: 0, base: 0 });
        self.drain_deferred_object_reads();
        let value = value?;
        self.ref_resolution.window_values.insert(cache_key, value.clone());
        Some((r, value))
    }

    /// A direct shared-array read may consume the exact typed window decoded
    /// before seeding closed. The array is relative to that window, not the
    /// allocation base. This authority does not cover casts, arithmetic,
    /// projections, mutable references, or locals with ambiguous definitions.
    pub(in crate::codegen_ay::chc) fn direct_fixed_array_window_value(
        &self,
        local: usize,
    ) -> Option<Expr> {
        use rustc_public::mir::{Mutability, Operand, Rvalue, StatementKind, TerminatorKind};
        let reference_ty = self.body.locals().get(local)?.ty;
        let TyKind::RigidTy(RigidTy::Ref(_, pointee, Mutability::Not)) = reference_ty.kind() else {
            return None;
        };
        if !matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Array(..)))
            || self.ty_has_interior_mut(pointee)
            || self.ref_resolution.deref_value_fact_dropped.contains(&local)
            || self
                .ref_resolution
                .subslice_offset
                .get(&local)
                .is_some_and(|offset| Self::const_usize_from_expr(offset) != Some(0))
        {
            return None;
        }
        let mut current = local;
        let mut seen = std::collections::HashSet::new();
        let constant = loop {
            if seen.len() >= 16
                || !seen.insert(current)
                || (current > 0 && current <= self.body.arg_locals().len())
                || self.body.locals().get(current)?.ty != reference_ty
                || self.local_has_multiple_whole_definitions(current)
            {
                // An argument has an implicit entry definition even when MIR
                // has only one later assignment. Do not use that future value
                // to answer a read of the caller's original reference.
                return None;
            }
            let mut unique = None;
            for block in &self.body.blocks {
                if !matches!(
                    block.terminator.kind,
                    TerminatorKind::Goto { .. }
                        | TerminatorKind::SwitchInt { .. }
                        | TerminatorKind::Resume
                        | TerminatorKind::Abort
                        | TerminatorKind::Return
                        | TerminatorKind::Unreachable
                        | TerminatorKind::Drop { .. }
                        | TerminatorKind::Call { .. }
                        | TerminatorKind::Assert { .. }
                ) {
                    // Inline-assembly outputs and any future write-capable
                    // terminators are outside this direct-definition proof.
                    return None;
                }
                for statement in &block.statements {
                    if let StatementKind::Assign(
                        _,
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place),
                    ) = &statement.kind
                        && place.local == current
                    {
                        // An alias of the reference slot can replace its
                        // pointer without a second whole-local assignment.
                        return None;
                    }
                    if let StatementKind::Assign(place, rhs) = &statement.kind
                        && place.local == current
                    {
                        if !place.projection.is_empty() || unique.is_some() {
                            return None;
                        }
                        unique = Some(rhs);
                    }
                }
                if let TerminatorKind::Call { destination, .. } = &block.terminator.kind
                    && destination.local == current
                {
                    return None;
                }
            }
            match unique? {
                Rvalue::Use(Operand::Constant(constant), _) => break constant,
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _)
                    if place.projection.is_empty() =>
                {
                    current = place.local
                }
                _ => return None,
            }
        };
        if constant.const_.ty() != reference_ty {
            return None;
        }
        let bytes = const_pointer::const_bytes(&constant.const_)?;
        let r = const_pointer::const_ref(&bytes, 0, pointee)?;
        let key = r.ptr.key()?;
        let object = self.global_object(&key)?;
        let fact = self.ref_resolution.const_ref_objects.get(&local)?;
        if object.fixed != Some(Fixedness::Fixed)
            || fact.obj_id != object.obj_id
            || fact.ptr != Some(r.ptr)
            || fact.offset != r.ptr.offset()
            || fact.nested.is_some()
        {
            return None;
        }
        let value =
            self.ref_resolution.window_values.get(&(key, r.ptr.offset(), r.metadata, pointee))?;
        (Self::translate_ty(pointee).as_ref() == Some(value.sort())).then(|| value.clone())
    }

    /// D10: the value fact of `dest = src + delta_elems` (elements of `src`'s
    /// pointee), for a KNOWN delta. A fact describes exactly one window:
    ///
    /// - through a known ZERO delta it is copied;
    /// - an ARRAY-sorted fact is copied, because `subslice_offset` re-indexes
    ///   it (#4022);
    /// - a scalar or datatype fact is RE-DECODED from the window at
    ///   `k + delta·size` in the fixed target (`const_pointer::fixed_pointee_at`),
    ///   never copied: `*ONE.add(1) == 1` PROVED when the fact about `*ONE` was
    ///   copied to `ONE + 1`, and a correct window value copied through
    ///   `E.add(1)` made `*E.add(1) == 2` prove;
    /// - otherwise there is no fact, and the memory path (seeded whole, D2)
    ///   answers.
    pub(in crate::codegen_ay::chc) fn moved_const_value_fact(
        &self,
        src_local: usize,
        dest_local: usize,
        delta_elems: i128,
    ) -> Option<Expr> {
        let value = self.ref_resolution.const_ref_values.get(&src_local)?;
        let locals = self.body.locals();
        let src_pointee = locals.get(src_local).and_then(|l| Self::deref_pointee_ty(l.ty));
        let dest_pointee = locals.get(dest_local).and_then(|l| Self::deref_pointee_ty(l.ty));
        // A cast to another pointee TYPE reads another window: a fact read at
        // `[u16; 2]` does not answer a read at `u8` (`W as *const u8` indexed
        // the u16 array fact by byte offset and certified a counterexample to
        // a true byte).
        let same_window_type = match (src_pointee, dest_pointee) {
            (Some(src), Some(dest)) => fact_types_compatible(src, dest),
            _ => true,
        };
        if same_window_type && (delta_elems == 0 || value.sort().is_array()) {
            return Some(value.clone());
        }
        let ptr = self.ref_resolution.const_ref_objects.get(&src_local)?.ptr?;
        let src_pointee = src_pointee?;
        let dest_pointee = dest_pointee?;
        let elem_size = i128::try_from(src_pointee.layout().ok()?.shape().size.bytes()).ok()?;
        let r = const_pointer::ConstRef { ptr, metadata: None };
        let window = const_pointer::fixed_pointee_at(
            self.tcx,
            &r,
            delta_elems.checked_mul(elem_size)?,
            dest_pointee,
        )?;
        let mut scratch = Vec::new();
        self.decode_window(&window, dest_pointee, &mut scratch, InitSite { obj_id: 0, base: 0 })
    }

    /// D10/D4: the object record of `dest = src + delta_elems`: the same
    /// object, the offset moved by `delta_elems·size`.
    pub(in crate::codegen_ay::chc) fn moved_const_ref_object(
        &self,
        src_local: usize,
        delta_elems: i128,
    ) -> Option<crate::codegen_ay::chc::codegen_ctx::ConstRefObject> {
        let object = self.ref_resolution.const_ref_objects.get(&src_local)?;
        if delta_elems == 0 {
            return Some(*object);
        }
        let src_pointee = Self::deref_pointee_ty(self.body.locals().get(src_local)?.ty)?;
        let elem_size = i128::try_from(src_pointee.layout().ok()?.shape().size.bytes()).ok()?;
        object.moved(delta_elems.checked_mul(elem_size)?)
    }

    fn mint_reachable_objects(&mut self, body: &rustc_public::mir::Body) {
        // Every target gets its one address, whatever block names it.
        let reachable = const_pointer::reachable_targets(self.tcx, body, |_| true);
        for reached in reachable.targets {
            self.mint_object(reached.key);
        }
        // D2's read set comes from the blocks that can CONTINUE (reach a
        // `Return` or a loop). A constant used only on a panic-only path — an
        // assertion message, a panic `Location` — is never read where a value
        // can change a verdict, and seeding its bytes only cost: an 89-byte
        // message became 89 entry-rule seeds and bb0 stores, and pushed
        // `lc_dual_guard_entry`'s loop-skipped harness off its straight-line
        // proof into a vacuous one.
        let may_continue =
            crate::codegen_ay::chc::decl::codegen_decl_panic_filter::compute_may_continue_blocks(
                body,
            );
        // Every pointer slot of every such constant — a constant pointer's own
        // value, or a pointer inside a constant VALUE (`HC.r`, `PTRS[1]`,
        // `REFS[0]`) — names its target as read at the slot's pointee type.
        // A message-only Kani hook (`kani::assert(c, "msg")`, `cover`,
        // `check`, a safety check) never dereferences its message: its
        // constants are values nothing reads, and seeding them only cost (a
        // loop contract's 89- and 68-byte messages).
        let message_only = |func: &rustc_public::mir::Operand| {
            use crate::kani_middle::kani_functions::KaniHook;
            crate::codegen_ay::chc::expr::codegen_expr_detect::kani_hook_in(body, func).is_some_and(
                |hook| {
                    matches!(
                        hook,
                        KaniHook::Assert
                            | KaniHook::Assume
                            | KaniHook::Check
                            | KaniHook::Cover
                            | KaniHook::SafetyCheck
                            | KaniHook::SafetyCheckNoAssume
                            | KaniHook::UnsupportedCheck
                            | KaniHook::Panic
                    )
                },
            )
        };
        for (bytes, ty) in const_pointer::body_constants_read(body, &may_continue, &message_only) {
            self.note_pointer_slots(&bytes, ty, 0);
        }
        // Every type the body dereferences at is a type a pointer into a fixed
        // object can be read at (a cast or byte offset changes the type without
        // a constant naming it).
        for ty in body_deref_read_types(body, &may_continue) {
            self.note_extra_read_type(ty);
        }
        // During translation (an inlined callee) the deferred notes are not
        // drained by a later seeding pass: drain them now, so a fixed object
        // read that can no longer be seeded is recorded.
        if self.ref_resolution.object_seeding_closed {
            self.drain_deferred_object_reads();
        }
    }

    /// Note, for every pointer slot of a value of type `ty` stored at `base`
    /// in `bytes` (a reference or raw pointer, found through structs, tuples,
    /// arrays and every enum variant), that its target is read at the slot's
    /// pointee type. A slot that holds no relocation (null, dangling, another
    /// variant's bytes) names nothing.
    pub(in crate::codegen_ay::chc) fn note_pointer_slots(
        &self,
        bytes: &dyn ConstRead,
        ty: Ty,
        base: usize,
    ) {
        let mut slots = Vec::new();
        pointer_slots(ty, base, &mut slots, POINTER_SLOT_DEPTH);
        for (at, pointee) in slots {
            if let Some(ptr) = bytes.stored_pointer(at)
                && let Some(key) = ptr.key()
            {
                self.note_object_read_deferred(key, pointee);
            }
        }
    }
}

/// Whether a value fact about a window read at type `src` answers a read of
/// the same pointer at type `dest`: the same type up to regions, or the same
/// ELEMENT type — an array, its slice and its element are views of one run of
/// elements that `subslice_offset` re-indexes (`&[u32; 3]` unsized to
/// `&[u32]`, or cast to `*const u32`). Any other cast reads another window.
pub(in crate::codegen_ay::chc) fn fact_types_compatible(src: Ty, dest: Ty) -> bool {
    use crate::codegen_ay::chc::decl::static_path::same_ty_modulo_regions;
    fn element(ty: Ty) -> Ty {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Array(elem, _) | RigidTy::Slice(elem)) => elem,
            TyKind::RigidTy(RigidTy::Str) => Ty::unsigned_ty(rustc_public::ty::UintTy::U8),
            _ => ty,
        }
    }
    same_ty_modulo_regions(src, dest) || same_ty_modulo_regions(element(src), element(dest))
}

/// The types `body` reads or writes through a pointer, in its blocks `keep`
/// selects: the pointee of every `Deref` in a place, and every field, element
/// or subslice type projected after it.
fn body_deref_read_types(body: &rustc_public::mir::Body, keep: &[bool]) -> Vec<Ty> {
    use rustc_public::mir::visit::{Location, PlaceContext};
    use rustc_public::mir::{LocalDecl, MirVisitor, Place, ProjectionElem};

    struct Derefs<'b> {
        locals: &'b [LocalDecl],
        out: Vec<Ty>,
    }
    impl Derefs<'_> {
        fn push(&mut self, ty: Ty) {
            if !self.out.contains(&ty) {
                self.out.push(ty);
            }
        }
    }
    impl MirVisitor for Derefs<'_> {
        fn visit_place(&mut self, place: &Place, ptx: PlaceContext, location: Location) {
            if let Some(local) = self.locals.get(place.local) {
                let mut ty = local.ty;
                let mut after_deref = false;
                for proj in &place.projection {
                    let next = match proj {
                        ProjectionElem::Deref => {
                            after_deref = true;
                            match ty.kind() {
                                TyKind::RigidTy(RigidTy::Ref(_, p, _) | RigidTy::RawPtr(p, _)) => {
                                    Some(p)
                                }
                                TyKind::RigidTy(RigidTy::Adt(def, args)) if def.is_box() => {
                                    args.0.first().and_then(|a| a.ty().copied())
                                }
                                _ => None,
                            }
                        }
                        ProjectionElem::Field(_, field_ty) => Some(*field_ty),
                        ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => {
                            match ty.kind() {
                                TyKind::RigidTy(RigidTy::Array(elem, _) | RigidTy::Slice(elem)) => {
                                    Some(elem)
                                }
                                _ => None,
                            }
                        }
                        ProjectionElem::Subslice { .. } | ProjectionElem::Downcast(_) => Some(ty),
                        ProjectionElem::OpaqueCast(cast_ty) => Some(*cast_ty),
                    };
                    let Some(next) = next else { break };
                    ty = next;
                    if after_deref {
                        self.push(ty);
                    }
                }
            }
            self.super_place(place, ptx, location);
        }
    }

    let mut derefs = Derefs { locals: body.locals(), out: Vec::new() };
    for (idx, block) in body.blocks.iter().enumerate() {
        if keep.get(idx).copied().unwrap_or(true) {
            derefs.visit_basic_block(block);
        }
    }
    derefs.out
}

/// How deep [`pointer_slots`] descends into nested aggregates.
const POINTER_SLOT_DEPTH: usize = 6;

/// The pointer slots of a value of type `ty` at byte `base`: `(offset, pointee)`
/// for every reference or raw-pointer field or element, through structs,
/// tuples, arrays and every enum variant, by rustc's layout offsets.
fn pointer_slots(ty: Ty, base: usize, out: &mut Vec<(usize, Ty)>, depth: usize) {
    use crate::kani_middle::abi::LayoutOf;
    let Some(depth) = depth.checked_sub(1) else { return };
    if out.len() > MAX_SEEDED_OBJECT_BYTES {
        return;
    }
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _)) => {
            out.push((base, pointee));
        }
        TyKind::RigidTy(RigidTy::Tuple(tys)) => {
            let layout = LayoutOf::new(ty);
            for (i, field_ty) in tys.iter().enumerate() {
                if let Some(off) = layout.field_offset(i) {
                    pointer_slots(*field_ty, base + off, out, depth);
                }
            }
        }
        TyKind::RigidTy(RigidTy::Array(elem, len)) => {
            let Ok(len) = len.eval_target_usize() else { return };
            let Some(size) = LayoutOf::new(elem).size_of().filter(|&s| s > 0) else { return };
            let count = (len as usize).min(MAX_SEEDED_OBJECT_BYTES / size + 1);
            for i in 0..count {
                pointer_slots(elem, base + i * size, out, depth);
            }
        }
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            let layout = LayoutOf::new(ty);
            for (v, variant) in def.variants().iter().enumerate() {
                for (f, field) in variant.fields().iter().enumerate() {
                    let off = if def.variants().len() == 1 {
                        layout.field_offset(f)
                    } else {
                        layout.variant_field_offset(v, f)
                    };
                    // A field whose type does not instantiate has no slots to
                    // name (the enumeration is best-effort, like its depth cap).
                    if let (Some(off), Some(field_ty)) = (off, mono_ty::field_ty(field, &args)) {
                        pointer_slots(field_ty, base + off, out, depth);
                    }
                }
            }
        }
        _ => {}
    }
}
